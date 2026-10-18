module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestScopeMarkers
public import Controller.Cost.ForestCounterFrame

@[expose] public section

/-!
# Scope-marker machine cells

The touch body tests one separate scope-marker cell and pushes a channel ID
only on its first touch. The reset body consumes a stored channel ID, computes
its marker address, and clears the cell. Its code is independent of the channel
ID. Counter-address, loaded-value and temporary registers are overwritten;
stack/output suffixes are retained frames. Initial marker allocation, loop
control and code construction require separate operational refinements.
-/
namespace Controller.Cost.ForestMarkerMachine

open Controller.Decoder Controller.Cost.GateProgram
open Controller.Cost.ForestCounter Controller.Cost.ForestScopeMarkers

/-- A reusable body consumes the next runtime channel ID from the stack. -/
def resetBody (width offset : ℕ) : ForestCounter.Code width :=
  [.pop 0, .constant 1 (word width offset), .add 0 0 1,
    .constant 2 (word width 0), .store 0 2]

@[simp] theorem resetBody_length (width offset : ℕ) : (resetBody width offset).length = 5 := rfl

/-- The marked path skips the store and push. Branch destinations are absolute. -/
def touchBody (width base address coordinate : ℕ) : ForestCounter.Code width :=
  [.constant 0 (word width address), .load 1 0,
    .branchZero 1 (word width (base + 5)),
    .constant 2 (word width 0), .branchZero 2 (word width (base + 9)),
    .constant 2 (word width 1), .store 0 2,
    .constant 0 (word width coordinate), .push 0]

@[simp] theorem touchBody_length (width base address coordinate : ℕ) :
    (touchBody width base address coordinate).length = 9 := rfl

private theorem advance_eq (heap : Array (Word width)) (cursor : ℕ)
    (address loaded temporary : Word width) (fits : cursor < 2 ^ width) :
    (counterState heap cursor address loaded temporary).advance =
      counterState heap (cursor + 1) address loaded temporary := by
  unfold State.advance counterState
  rw [show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem put_loaded (heap : Array (Word width)) (cursor : ℕ)
    (address loaded temporary value : Word width) :
    (counterState heap cursor address loaded temporary).put 1 value =
      counterState heap cursor address value temporary := by
  unfold State.put counterState
  congr 1
  funext register
  by_cases first : register = 0
  · subst register; simp
  · by_cases second : register = 1 <;> simp [first, second]

private theorem put_address (heap : Array (Word width)) (cursor : ℕ)
    (address loaded temporary value : Word width) :
    (counterState heap cursor address loaded temporary).put 0 value =
      counterState heap cursor value loaded temporary := by
  unfold State.put counterState
  congr 1
  funext register
  by_cases first : register = 0 <;> simp [first]

theorem pop_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : ℕ) (address loaded temporary channel : Word width)
    (fits : cursor < 2 ^ width) (fetched : program[cursor]? = some (.pop 0)) :
    programStep program ((counterState heap cursor address loaded temporary).frame [channel] []) =
      some (counterState heap (cursor + 1) channel loaded temporary) := by
  unfold programStep
  rw [show ((counterState heap cursor address loaded temporary).frame [channel] []).pc.val = cursor from
    Nat.mod_eq_of_lt fits, fetched]
  change step (.pop (0 : Fin 4))
    ((counterState heap cursor address loaded temporary).frame [channel] []) = _
  simp only [step, State.frame, counterState, Bool.false_eq_true, ite_false,
    List.nil_append]
  change some ((counterState heap cursor address loaded temporary).advance.put 0 channel) = _
  rw [advance_eq heap cursor address loaded temporary fits, put_address]
  rfl

theorem constant_loaded_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : ℕ) (address loaded temporary value : Word width)
    (fits : cursor < 2 ^ width) (fetched : program[cursor]? = some (.constant 1 value)) :
    programStep program (counterState heap cursor address loaded temporary) =
      some (counterState heap (cursor + 1) address value temporary) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded temporary).pc.val = cursor from
    Nat.mod_eq_of_lt fits, fetched]
  change step (.constant (1 : Fin 4) value) (counterState heap cursor address loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap cursor address loaded temporary).advance.put 1 value) = _
  rw [advance_eq heap cursor address loaded temporary fits, put_loaded]
  rfl

theorem add_address_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : ℕ) (address loaded temporary : Word width)
    (fits : cursor < 2 ^ width) (fetched : program[cursor]? = some (.add 0 0 1)) :
    programStep program (counterState heap cursor address loaded temporary) =
      some (counterState heap (cursor + 1) (word width (address.val + loaded.val)) loaded temporary) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded temporary).pc.val = cursor from
    Nat.mod_eq_of_lt fits, fetched]
  change step (.add (0 : Fin 4) 0 1) (counterState heap cursor address loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap cursor address loaded temporary).advance.put 0
    (word width (address.val + loaded.val))) = _
  rw [advance_eq heap cursor address loaded temporary fits, put_address]
  rfl

theorem store_temporary_transition (program : Program width 4) (heap : Array (Word width))
    (cursor address : ℕ) (loaded temporary : Word width)
    (fits : cursor < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (fetched : program[cursor]? = some (.store 0 2)) :
    programStep program (counterState heap cursor (word width address) loaded temporary) =
      some (counterState (heap.set address temporary) (cursor + 1)
        (word width address) loaded temporary) := by
  unfold programStep
  rw [show (counterState heap cursor (word width address) loaded temporary).pc.val = cursor from
    Nat.mod_eq_of_lt fits, fetched]
  change step (.store (0 : Fin 4) 2) (counterState heap cursor (word width address) loaded temporary) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change (if valid : (word width address).val < heap.size then
    some { (counterState heap cursor (word width address) loaded temporary).advance with
      heap := heap.set (word width address).val temporary } else none) = _
  rw [show (word width address).val = address from Nat.mod_eq_of_lt addressFits, dite_eq_left valid]
  rw [advance_eq heap cursor (word width address) loaded temporary fits]
  rfl

theorem branch_transition (program : Program width 4) (heap : Array (Word width))
    (cursor target : ℕ) (selector : Fin 4) (address loaded temporary : Word width)
    (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.branchZero selector (word width target))) :
    programStep program (counterState heap cursor address loaded temporary) =
      some (counterState heap
        (if ((counterState heap cursor address loaded temporary).reg selector).val = 0
          then target else cursor + 1) address loaded temporary) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded temporary).pc.val = cursor from
    Nat.mod_eq_of_lt fits, fetched]
  change step (.branchZero selector (word width target))
    (counterState heap cursor address loaded temporary) = _
  simp only [step, show (counterState heap cursor address loaded temporary).halted = false from rfl,
    Bool.false_eq_true, ite_false]
  rw [advance_eq heap cursor address loaded temporary fits]
  split <;> rfl

theorem push_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : ℕ) (address loaded temporary : Word width) (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.push 0)) :
    programStep program (counterState heap cursor address loaded temporary) =
      some ((counterState heap (cursor + 1) address loaded temporary).frame [address] []) := by
  unfold programStep
  rw [show (counterState heap cursor address loaded temporary).pc.val = cursor from
    Nat.mod_eq_of_lt fits, fetched]
  change step (.push (0 : Fin 4)) (counterState heap cursor address loaded temporary) = _
  simp only [step, show (counterState heap cursor address loaded temporary).halted = false from rfl,
    Bool.false_eq_true, ite_false]
  rw [advance_eq heap cursor address loaded temporary fits]
  rfl

/-- An already marked cell is read but neither stored nor pushed. -/
theorem marked_touch_execution (program : Program width 4) (heap : Array (Word width))
    (base address coordinate : ℕ) (oldAddress oldLoaded oldTemporary : Word width)
    (programFits : base + 9 < 2 ^ width) (addressFits : address < 2 ^ width)
    (oneFits : 1 < 2 ^ width) (valid : address < heap.size)
    (marked : heap[address] = word width 1)
    (block : BlockAt program base (touchBody width base address coordinate)) :
    Execution program (counterState heap base oldAddress oldLoaded oldTemporary)
      (counterState heap (base + 9) (word width address) (word width 1) (word width 0))
      5 (5 + heap.size) := by
  have first : program[base]? = some (.constant 0 (word width address)) := by
    simpa [touchBody] using block 0 (by simp)
  have second : program[base + 1]? = some (.load 1 0) := by
    simpa [touchBody] using block 1 (by simp)
  have third : program[base + 2]? = some (.branchZero 1 (word width (base + 5))) := by
    simpa [touchBody] using block 2 (by simp)
  have fourth : program[base + 3]? = some (.constant 2 (word width 0)) := by
    simpa [touchBody] using block 3 (by simp)
  have fifth : program[base + 4]? = some (.branchZero 2 (word width (base + 9))) := by
    simpa [touchBody] using block 4 (by simp)
  have firstStep := address_transition program heap base address oldAddress oldLoaded oldTemporary
    (by omega) first
  have secondStep := read_transition program heap (base + 1) address oldLoaded oldTemporary
    (word width 1) (by omega) addressFits valid marked second
  have thirdStep := branch_transition program heap (base + 2) (base + 5) 1
    (word width address) (word width 1) oldTemporary (by omega) third
  have one : ((counterState heap (base + 2) (word width address) (word width 1)
      oldTemporary).reg (1 : Fin 4)).val = 1 := by
    simp only [counterState]
    exact Nat.mod_eq_of_lt oneFits
  rw [one, ite_eq_right (by decide : (1 : ℕ) ≠ 0)] at thirdStep
  have fourthStep := increment_transition program heap (base + 3) 0
    (word width address) (word width 1) oldTemporary (by omega) fourth
  have fifthStep := branch_transition program heap (base + 4) (base + 9) 2
    (word width address) (word width 1) (word width 0) (by omega) fifth
  have zero : ((counterState heap (base + 4) (word width address) (word width 1)
      (word width 0)).reg (2 : Fin 4)).val = 0 := by simp [counterState, word]
  rw [zero, ite_eq_left rfl] at fifthStep
  simp only [Nat.add_assoc] at secondStep thirdStep fourthStep fifthStep
  have trace := Execution.cons firstStep (Execution.cons secondStep (Execution.cons thirdStep
    (Execution.cons fourthStep (Execution.cons fifthStep (Execution.refl
      (counterState heap (base + 9) (word width address) (word width 1) (word width 0)))))))
  simpa [counterState_liveWords] using trace

/-- A fresh touch stores one and pushes one runtime channel ID. -/
theorem fresh_touch_execution (program : Program width 4) (heap : Array (Word width))
    (base address coordinate : ℕ) (oldAddress oldLoaded oldTemporary : Word width)
    (programFits : base + 9 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (unmarked : heap[address] = word width 0)
    (block : BlockAt program base (touchBody width base address coordinate)) :
    Execution program (counterState heap base oldAddress oldLoaded oldTemporary)
      ((counterState (heap.set address (word width 1)) (base + 9)
        (word width coordinate) (word width 0) (word width 1)).frame [word width coordinate] [])
      7 (6 + heap.size) := by
  have first : program[base]? = some (.constant 0 (word width address)) := by
    simpa [touchBody] using block 0 (by simp)
  have second : program[base + 1]? = some (.load 1 0) := by
    simpa [touchBody] using block 1 (by simp)
  have third : program[base + 2]? = some (.branchZero 1 (word width (base + 5))) := by
    simpa [touchBody] using block 2 (by simp)
  have fourth : program[base + 5]? = some (.constant 2 (word width 1)) := by
    simpa [touchBody] using block 5 (by simp)
  have fifth : program[base + 6]? = some (.store 0 2) := by
    simpa [touchBody] using block 6 (by simp)
  have sixth : program[base + 7]? = some (.constant 0 (word width coordinate)) := by
    simpa [touchBody] using block 7 (by simp)
  have seventh : program[base + 8]? = some (.push 0) := by
    simpa [touchBody] using block 8 (by simp)
  have firstStep := address_transition program heap base address oldAddress oldLoaded oldTemporary
    (by omega) first
  have secondStep := read_transition program heap (base + 1) address oldLoaded oldTemporary
    (word width 0) (by omega) addressFits valid unmarked second
  have thirdStep := branch_transition program heap (base + 2) (base + 5) 1
    (word width address) (word width 0) oldTemporary (by omega) third
  have zero : ((counterState heap (base + 2) (word width address) (word width 0)
      oldTemporary).reg (1 : Fin 4)).val = 0 := by simp [counterState, word]
  rw [zero, ite_eq_left rfl] at thirdStep
  have fourthStep := increment_transition program heap (base + 5) 1
    (word width address) (word width 0) oldTemporary (by omega) fourth
  have fifthStep := store_temporary_transition program heap (base + 6) address
    (word width 0) (word width 1) (by omega) addressFits valid fifth
  have sixthStep := address_transition program (heap.set address (word width 1)) (base + 7)
    coordinate (word width address) (word width 0) (word width 1) (by omega) sixth
  have seventhStep := push_transition program (heap.set address (word width 1)) (base + 8)
    (word width coordinate) (word width 0) (word width 1) (by omega) seventh
  simp only [Nat.add_assoc] at secondStep thirdStep fourthStep fifthStep sixthStep seventhStep
  have trace := Execution.cons firstStep (Execution.cons secondStep (Execution.cons thirdStep
    (Execution.cons fourthStep (Execution.cons fifthStep (Execution.cons sixthStep
      (Execution.cons seventhStep (Execution.refl
        ((counterState (heap.set address (word width 1)) (base + 9)
          (word width coordinate) (word width 0) (word width 1)).frame [word width coordinate] []))))))))
  convert trace using 1 <;> simp only [counterState_liveWords, State.frame_liveWords,
    List.length_cons, List.length_nil, Nat.add_zero, Array.size_set] <;> omega

/-- Five actual fetched instructions clear the marker selected by a runtime
stack word. No channel-specific clear code is generated. -/
theorem reset_execution (program : Program width 4) (heap : Array (Word width))
    (base offset channel : ℕ) (oldAddress oldLoaded oldTemporary : Word width)
    (programFits : base + 5 < 2 ^ width) (addressFits : offset + channel < 2 ^ width)
    (valid : offset + channel < heap.size)
    (block : BlockAt program base (resetBody width offset)) :
    Execution program
      ((counterState heap base oldAddress oldLoaded oldTemporary).frame [word width channel] [])
      (counterState (heap.set (offset + channel) (word width 0)) (base + 5)
        (word width (offset + channel)) (word width offset) (word width 0))
      5 (6 + heap.size) := by
  have first : program[base]? = some (.pop 0) := by simpa [resetBody] using block 0 (by simp)
  have second : program[base + 1]? = some (.constant 1 (word width offset)) := by
    simpa [resetBody] using block 1 (by simp)
  have third : program[base + 2]? = some (.add 0 0 1) := by
    simpa [resetBody] using block 2 (by simp)
  have fourth : program[base + 3]? = some (.constant 2 (word width 0)) := by
    simpa [resetBody] using block 3 (by simp)
  have fifth : program[base + 4]? = some (.store 0 2) := by
    simpa [resetBody] using block 4 (by simp)
  have firstStep := pop_transition program heap base oldAddress oldLoaded oldTemporary
    (word width channel) (by omega) first
  have secondStep := constant_loaded_transition program heap (base + 1) (word width channel)
    oldLoaded oldTemporary (word width offset) (by omega) second
  have thirdStep := add_address_transition program heap (base + 2) (word width channel)
    (word width offset) oldTemporary (by omega) third
  have sumWord : word width ((word width channel).val + (word width offset).val) =
      word width (offset + channel) := by
    rw [show (word width channel).val = channel from Nat.mod_eq_of_lt (by omega),
      show (word width offset).val = offset from Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  rw [sumWord] at thirdStep
  have fourthStep := increment_transition program heap (base + 3) 0
    (word width (offset + channel)) (word width offset) oldTemporary (by omega) fourth
  have fifthStep := store_temporary_transition program heap (base + 4) (offset + channel)
    (word width offset) (word width 0) (by omega) addressFits valid fifth
  simp only [Nat.add_assoc] at secondStep thirdStep fourthStep fifthStep
  have trace := Execution.cons firstStep (Execution.cons secondStep (Execution.cons thirdStep
    (Execution.cons fourthStep (Execution.cons fifthStep (Execution.refl
      (counterState (heap.set (offset + channel) (word width 0)) (base + 5)
        (word width (offset + channel)) (word width offset) (word width 0)))))))
  convert trace using 1 <;> simp only [counterState_liveWords, State.frame_liveWords,
    List.length_cons, List.length_nil, Nat.add_zero, Array.size_set] <;> omega

/-- Popping a touched ID preserves a trailing stack/output frame. The frame is
charged throughout the execution and contains no implicit saved registers. -/
theorem reset_execution_framed (program : Program width 4) (heap : Array (Word width))
    (base offset channel : ℕ) (oldAddress oldLoaded oldTemporary : Word width)
    (stack output : List (Word width))
    (programFits : base + 5 < 2 ^ width) (addressFits : offset + channel < 2 ^ width)
    (valid : offset + channel < heap.size)
    (block : BlockAt program base (resetBody width offset)) :
    Execution program
      ((counterState heap base oldAddress oldLoaded oldTemporary).frame (word width channel :: stack) output)
      ((counterState (heap.set (offset + channel) (word width 0)) (base + 5)
        (word width (offset + channel)) (word width offset) (word width 0)).frame stack output)
      5 (6 + heap.size + (stack.length + output.length)) := by
  have trace := reset_execution program heap base offset channel oldAddress oldLoaded oldTemporary
    programFits addressFits valid block
  simpa only [State.frame, List.nil_append, List.singleton_append, List.append_assoc] using
    trace.frame stack output

theorem marked_touch_execution_framed (program : Program width 4) (heap : Array (Word width))
    (base address coordinate : ℕ) (oldAddress oldLoaded oldTemporary : Word width)
    (stack output : List (Word width))
    (programFits : base + 9 < 2 ^ width) (addressFits : address < 2 ^ width)
    (oneFits : 1 < 2 ^ width) (valid : address < heap.size)
    (marked : heap[address] = word width 1)
    (block : BlockAt program base (touchBody width base address coordinate)) :
    Execution program ((counterState heap base oldAddress oldLoaded oldTemporary).frame stack output)
      ((counterState heap (base + 9) (word width address) (word width 1) (word width 0)).frame stack output)
      5 (5 + heap.size + (stack.length + output.length)) := by
  exact (marked_touch_execution program heap base address coordinate oldAddress oldLoaded oldTemporary
    programFits addressFits oneFits valid marked block).frame stack output

theorem fresh_touch_execution_framed (program : Program width 4) (heap : Array (Word width))
    (base address coordinate : ℕ) (oldAddress oldLoaded oldTemporary : Word width)
    (stack output : List (Word width))
    (programFits : base + 9 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (unmarked : heap[address] = word width 0)
    (block : BlockAt program base (touchBody width base address coordinate)) :
    Execution program ((counterState heap base oldAddress oldLoaded oldTemporary).frame stack output)
      ((counterState (heap.set address (word width 1)) (base + 9)
        (word width coordinate) (word width 0) (word width 1)).frame (word width coordinate :: stack) output)
      7 (6 + heap.size + (stack.length + output.length)) := by
  have trace := fresh_touch_execution program heap base address coordinate oldAddress oldLoaded oldTemporary
    programFits addressFits valid unmarked block
  simpa only [State.frame, List.nil_append, List.singleton_append, List.append_assoc] using
    trace.frame stack output

/-- Removing the stack head clears precisely that channel's scope mark. -/
def clearHead (state : MarkState n) (coordinate : Channel n) (rest : List (Channel n)) : MarkState n :=
  ⟨clear state.marked coordinate, rest⟩

theorem clearHead_wellFormed (state : MarkState n) (coordinate : Channel n)
    (rest : List (Channel n)) (head : state.touched = coordinate :: rest)
    (well : WellFormed state) : WellFormed (clearHead state coordinate rest) := by
  have unique : (coordinate :: rest).Nodup := by simpa only [head] using well.1
  have fresh := (List.nodup_cons.mp unique).1
  refine ⟨(List.nodup_cons.mp unique).2, ?_⟩
  intro current
  by_cases same : current = coordinate
  · subst current
    simp [clearHead, clear, fresh]
  · change (if current = coordinate then false else state.marked current) = true ↔ current ∈ rest
    rw [ite_eq_right same, well.2 current, head]
    simp only [List.mem_cons, same, false_or]

theorem clearHead_stored (width offset : ℕ) (heap : Array (Word width))
    (state : MarkState n) (coordinate : Channel n) (rest : List (Channel n))
    (stored : MarkersStored heap offset state) :
    MarkersStored (heap.set (offset + coordinate.val) (word width 0) (stored.valid coordinate)) offset
      (clearHead state coordinate rest) := by
  refine ⟨fun other => by simpa using stored.valid other, ?_⟩
  intro other
  by_cases same : other = coordinate
  · subst other
    rw [Array.getElem_set_self (stored.valid coordinate)]
    simp [clearHead, clear]
  · have different : offset + coordinate.val ≠ offset + other.val := by
      intro equal
      have values : coordinate.val = other.val := by omega
      exact same (Fin.ext values.symm)
    rw [Array.getElem_set_ne (stored.valid coordinate) (stored.valid other) different, stored.held other]
    simp only [clearHead, clear, same, ite_false]

/-- A checked runtime pop-clear body preserves the logical touched-list invariant
and the indexed marker representation. Its caller supplies loop control. -/
theorem reset_refines (program : Program width 4) (heap : Array (Word width))
    (base offset : ℕ) (state : MarkState n) (coordinate : Channel n) (rest : List (Channel n))
    (oldAddress oldLoaded oldTemporary : Word width) (stack output : List (Word width))
    (head : state.touched = coordinate :: rest) (well : WellFormed state)
    (stored : MarkersStored heap offset state)
    (programFits : base + 5 < 2 ^ width) (addressFits : offset + coordinate.val < 2 ^ width)
    (block : BlockAt program base (resetBody width offset)) :
    Execution program
      ((counterState heap base oldAddress oldLoaded oldTemporary).frame
        (word width coordinate.val :: stack) output)
      ((counterState (heap.set (offset + coordinate.val) (word width 0) (stored.valid coordinate)) (base + 5)
        (word width (offset + coordinate.val)) (word width offset) (word width 0)).frame stack output)
      5 (6 + heap.size + (stack.length + output.length)) ∧
    WellFormed (clearHead state coordinate rest) ∧
    MarkersStored (heap.set (offset + coordinate.val) (word width 0) (stored.valid coordinate)) offset
      (clearHead state coordinate rest) := by
  exact ⟨reset_execution_framed program heap base offset coordinate.val oldAddress oldLoaded
    oldTemporary stack output programFits addressFits (stored.valid coordinate) block,
    clearHead_wellFormed state coordinate rest head well,
    clearHead_stored width offset heap state coordinate rest stored⟩

end Controller.Cost.ForestMarkerMachine
