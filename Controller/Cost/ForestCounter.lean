module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.GateProgram
public import Controller.Decoder.ForestGeneric

@[expose] public section

/-!
# Guard-counter machine cells

A cell reads, changes and stores one indexed guard counter using five actual
instructions. Word representability and valid heap addresses are explicit.
The cell preserves heap, stack and output sizes. Whole-forest visitation,
weight arithmetic and sparse initialization have separate obligations.
-/
namespace Controller.Cost.ForestCounter

open Controller.Decoder
open Controller.Cost.GateProgram

abbrev Code (width : Nat) := List (Instruction width 4)

/-- Registers hold address, counter, increment and an unused zero word. -/
def counterState (heap : Array (Word width)) (cursor : Nat)
    (address counter increment : Word width) : State width 4 where
  reg := fun register => if register = 0 then address else if register = 1 then counter
    else if register = 2 then increment else word width 0
  heap := heap
  stack := []
  output := []
  pc := word width cursor
  halted := false

@[simp] theorem counterState_liveWords (heap : Array (Word width)) (cursor : Nat)
    (address counter increment : Word width) :
    (counterState heap cursor address counter increment).liveWords = 5 + heap.size := by
  simp [counterState, State.liveWords]
  omega

/-- Entry uses increment one. Exit uses the modular additive inverse of one. -/
def changeCode (width address increment : Nat) : Code width :=
  [.constant 0 (word width address), .load 1 0,
    .constant 2 (word width increment), .add 1 1 2, .store 0 1]

@[simp] theorem changeCode_length (width address increment : Nat) :
    (changeCode width address increment).length = 5 := rfl

private theorem encoded_value (width value : Nat) (fits : value < 2 ^ width) :
    (word width value).val = value := Nat.mod_eq_of_lt fits

private theorem counterState_advance (heap : Array (Word width)) (cursor : Nat)
    (address counter increment : Word width) (fits : cursor < 2 ^ width) :
    (counterState heap cursor address counter increment).advance =
      counterState heap (cursor + 1) address counter increment := by
  unfold State.advance counterState
  rw [encoded_value width cursor fits]

private theorem counterState_put_address (heap : Array (Word width)) (cursor : Nat)
    (address counter increment next : Word width) :
    (counterState heap cursor address counter increment).put 0 next =
      counterState heap cursor next counter increment := by
  unfold State.put counterState
  congr 1
  funext register
  by_cases first : register = 0 <;> simp [first]

private theorem counterState_put_counter (heap : Array (Word width)) (cursor : Nat)
    (address counter increment next : Word width) :
    (counterState heap cursor address counter increment).put 1 next =
      counterState heap cursor address next increment := by
  unfold State.put counterState
  congr 1
  funext register
  by_cases first : register = 0
  · subst register; simp
  · by_cases second : register = 1 <;> simp [first, second]

private theorem counterState_put_increment (heap : Array (Word width)) (cursor : Nat)
    (address counter increment next : Word width) :
    (counterState heap cursor address counter increment).put 2 next =
      counterState heap cursor address counter next := by
  unfold State.put counterState
  congr 1
  funext register
  by_cases first : register = 0
  · subst register; simp
  · by_cases second : register = 1
    · subst register; simp
    · by_cases third : register = 2 <;> simp [first, second, third]

theorem address_transition (program : Program width 4) (heap : Array (Word width))
    (cursor address : Nat) (oldAddress counter increment : Word width)
    (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.constant 0 (word width address))) :
    programStep program (counterState heap cursor oldAddress counter increment) =
      some (counterState heap (cursor + 1) (word width address) counter increment) := by
  unfold programStep
  rw [show (counterState heap cursor oldAddress counter increment).pc.val = cursor from
    encoded_value width cursor fits, fetched]
  change step (.constant (0 : Fin 4) (word width address))
    (counterState heap cursor oldAddress counter increment) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap cursor oldAddress counter increment).advance.put 0
    (word width address)) = _
  rw [counterState_advance heap cursor oldAddress counter increment fits,
    counterState_put_address]
  rfl

theorem read_transition (program : Program width 4) (heap : Array (Word width))
    (cursor address : Nat) (oldCounter increment loaded : Word width)
    (cursorFits : cursor < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (stored : heap[address] = loaded)
    (fetched : program[cursor]? = some (.load 1 0)) :
    programStep program (counterState heap cursor (word width address) oldCounter increment) =
      some (counterState heap (cursor + 1) (word width address) loaded increment) := by
  unfold programStep
  rw [show (counterState heap cursor (word width address) oldCounter increment).pc.val = cursor from
    encoded_value width cursor cursorFits, fetched]
  change step (.load (1 : Fin 4) (0 : Fin 4))
    (counterState heap cursor (word width address) oldCounter increment) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change (if h : (word width address).val < heap.size then
    some ((counterState heap cursor (word width address) oldCounter increment).advance.put 1
      heap[(word width address).val]) else none) = _
  rw [dite_eq_left (by simpa [encoded_value width address addressFits] using valid)]
  simp only [encoded_value width address addressFits, stored]
  rw [counterState_advance heap cursor (word width address) oldCounter increment cursorFits,
    counterState_put_counter]
  rfl

theorem increment_transition (program : Program width 4) (heap : Array (Word width))
    (cursor delta : Nat) (address counter oldIncrement : Word width)
    (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.constant 2 (word width delta))) :
    programStep program (counterState heap cursor address counter oldIncrement) =
      some (counterState heap (cursor + 1) address counter (word width delta)) := by
  unfold programStep
  rw [show (counterState heap cursor address counter oldIncrement).pc.val = cursor from
    encoded_value width cursor fits, fetched]
  change step (.constant (2 : Fin 4) (word width delta))
    (counterState heap cursor address counter oldIncrement) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap cursor address counter oldIncrement).advance.put 2
    (word width delta)) = _
  rw [counterState_advance heap cursor address counter oldIncrement fits,
    counterState_put_increment]
  rfl

theorem add_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : Nat) (address counter increment : Word width)
    (fits : cursor < 2 ^ width)
    (fetched : program[cursor]? = some (.add 1 1 2)) :
    programStep program (counterState heap cursor address counter increment) =
      some (counterState heap (cursor + 1) address
        (word width (counter.val + increment.val)) increment) := by
  unfold programStep
  rw [show (counterState heap cursor address counter increment).pc.val = cursor from
    encoded_value width cursor fits, fetched]
  change step (.add (1 : Fin 4) (1 : Fin 4) (2 : Fin 4))
    (counterState heap cursor address counter increment) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change some ((counterState heap cursor address counter increment).advance.put 1
    (word width (counter.val + increment.val))) = _
  rw [counterState_advance heap cursor address counter increment fits,
    counterState_put_counter]
  rfl

theorem store_transition (program : Program width 4) (heap : Array (Word width))
    (cursor address : Nat) (counter increment : Word width)
    (cursorFits : cursor < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size)
    (fetched : program[cursor]? = some (.store 0 1)) :
    programStep program (counterState heap cursor (word width address) counter increment) =
      some (counterState (heap.set address counter) (cursor + 1)
        (word width address) counter increment) := by
  unfold programStep
  rw [show (counterState heap cursor (word width address) counter increment).pc.val = cursor from
    encoded_value width cursor cursorFits, fetched]
  change step (.store (0 : Fin 4) (1 : Fin 4))
    (counterState heap cursor (word width address) counter increment) = _
  simp only [step, counterState, Bool.false_eq_true, ite_false]
  change (if h : (word width address).val < heap.size then
    some { (counterState heap cursor (word width address) counter increment).advance with
      heap := heap.set (word width address).val counter } else none) = _
  rw [dite_eq_left (by simpa [encoded_value width address addressFits] using valid)]
  simp only [encoded_value width address addressFits]
  rw [counterState_advance heap cursor (word width address) counter increment cursorFits]
  rfl

/-- Five real fetched transitions update one counter; no cell allocation occurs. -/
theorem change_execution (program : Program width 4) (heap : Array (Word width))
    (base address delta : Nat) (oldAddress oldCounter oldIncrement storedCounter : Word width)
    (programFits : base + 5 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (stored : heap[address] = storedCounter)
    (block : BlockAt program base (changeCode width address delta)) :
    Execution program (counterState heap base oldAddress oldCounter oldIncrement)
      (counterState (heap.set address (word width (storedCounter.val + (word width delta).val)))
        (base + 5) (word width address)
        (word width (storedCounter.val + (word width delta).val)) (word width delta))
      5 (5 + heap.size) := by
  have first : program[base]? = some (.constant 0 (word width address)) := by
    simpa [changeCode] using block 0 (by simp)
  have second : program[base + 1]? = some (.load 1 0) := by
    simpa [changeCode] using block 1 (by simp)
  have third : program[base + 2]? = some (.constant 2 (word width delta)) := by
    simpa [changeCode] using block 2 (by simp)
  have fourth : program[base + 3]? = some (.add 1 1 2) := by
    simpa [changeCode] using block 3 (by simp)
  have fifth : program[base + 4]? = some (.store 0 1) := by
    simpa [changeCode] using block 4 (by simp)
  have firstStep := address_transition program heap base address oldAddress oldCounter oldIncrement
    (by omega) first
  have secondStep := read_transition program heap (base + 1) address oldCounter oldIncrement
    storedCounter (by omega) addressFits valid stored second
  have thirdStep := increment_transition program heap (base + 2) delta (word width address)
    storedCounter oldIncrement (by omega) third
  have fourthStep := add_transition program heap (base + 3) (word width address)
    storedCounter (word width delta) (by omega) fourth
  have fifthStep := store_transition program heap (base + 4) address
    (word width (storedCounter.val + (word width delta).val)) (word width delta)
    (by omega) addressFits valid fifth
  simp only [Nat.add_assoc] at secondStep thirdStep fourthStep fifthStep
  have trace := Execution.cons firstStep (Execution.cons secondStep (Execution.cons thirdStep
    (Execution.cons fourthStep (Execution.cons fifthStep (Execution.refl
      (counterState (heap.set address (word width (storedCounter.val + (word width delta).val)))
        (base + 5) (word width address)
        (word width (storedCounter.val + (word width delta).val)) (word width delta)))))))
  simpa [counterState_liveWords] using trace

/-- Entry is natural counter increment when the incremented value fits the word. -/
theorem entry_execution (program : Program width 4) (heap : Array (Word width))
    (base address count : Nat) (oldAddress oldCounter oldIncrement : Word width)
    (programFits : base + 5 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (stored : heap[address] = word width count)
    (countFits : count + 1 < 2 ^ width)
    (block : BlockAt program base (changeCode width address 1)) :
    Execution program (counterState heap base oldAddress oldCounter oldIncrement)
      (counterState (heap.set address (word width (count + 1))) (base + 5)
        (word width address) (word width (count + 1)) (word width 1))
      5 (5 + heap.size) := by
  have trace := change_execution program heap base address 1 oldAddress oldCounter oldIncrement
    (word width count) programFits addressFits valid stored block
  simpa [encoded_value width count (by omega), encoded_value width 1 (by omega)] using trace

/-- Exit decrements positive counters by adding the modular inverse of one. -/
theorem exit_word (width count : Nat) (positive : 0 < count) (fits : count < 2 ^ width) :
    word width ((word width count).val + (word width (2 ^ width - 1)).val) =
      word width (count - 1) := by
  have capacity : 0 < 2 ^ width := Nat.two_pow_pos width
  rw [encoded_value width count fits, encoded_value width (2 ^ width - 1) (by omega)]
  apply Fin.ext
  change (count + (2 ^ width - 1)) % (2 ^ width) = (count - 1) % (2 ^ width)
  have arithmetic : count + (2 ^ width - 1) = (count - 1) + 2 ^ width := by omega
  rw [arithmetic, Nat.add_mod_right]

/-- A path-exit cell restores the preceding counter value without changing storage. -/
theorem exit_execution (program : Program width 4) (heap : Array (Word width))
    (base address count : Nat) (oldAddress oldCounter oldIncrement : Word width)
    (programFits : base + 5 < 2 ^ width) (addressFits : address < 2 ^ width)
    (valid : address < heap.size) (stored : heap[address] = word width count)
    (positive : 0 < count) (countFits : count < 2 ^ width)
    (block : BlockAt program base (changeCode width address (2 ^ width - 1))) :
    Execution program (counterState heap base oldAddress oldCounter oldIncrement)
      (counterState (heap.set address (word width (count - 1))) (base + 5)
        (word width address) (word width (count - 1)) (word width (2 ^ width - 1)))
      5 (5 + heap.size) := by
  have trace := change_execution program heap base address (2 ^ width - 1)
    oldAddress oldCounter oldIncrement (word width count) programFits addressFits valid stored block
  simpa only [exit_word width count positive countFits] using trace

/-- The channel counter array occupies a fixed indexed heap interval. This is
an invariant, not a request to scan or initialize that interval per root. -/
structure CountersStored (heap : Array (Word width)) (offset : Nat)
    (counters : GuardCounters n) : Prop where
  valid : ∀ channel : Channel n, offset + channel.val < heap.size
  held : ∀ channel : Channel n, heap[offset + channel.val]'(valid channel) = word width (counters channel)

/-- One actual cell store represents precisely the semantic one-label entry. -/
theorem countersStored_enter (heap : Array (Word width)) (offset : Nat)
    (counters : GuardCounters n) (channel : Channel n)
    (stored : CountersStored heap offset counters) :
    CountersStored (heap.set (offset + channel.val) (word width (counters channel + 1)) (stored.valid channel))
      offset (enterGuards counters [channel]) := by
  refine ⟨fun other => by simpa using stored.valid other, ?_⟩
  intro other
  by_cases same : other = channel
  · subst other
    rw [Array.getElem_set_self (stored.valid channel), enterGuards_count]
    simp
  · have addressDifferent : offset + channel.val ≠ offset + other.val := by
      intro equal
      have values : channel.val = other.val := by omega
      exact same (Fin.ext values.symm)
    rw [Array.getElem_set_ne (stored.valid channel) (stored.valid other) addressDifferent]
    rw [stored.held other, enterGuards_count]
    simp [same, Ne.symm same]

/-- One path-exit store represents precisely the semantic one-label removal. -/
theorem countersStored_leave (heap : Array (Word width)) (offset : Nat)
    (counters : GuardCounters n) (channel : Channel n)
    (stored : CountersStored heap offset counters) :
    CountersStored (heap.set (offset + channel.val) (word width (counters channel - 1)) (stored.valid channel))
      offset (leaveGuards counters [channel]) := by
  refine ⟨fun other => by simpa using stored.valid other, ?_⟩
  intro other
  by_cases same : other = channel
  · subst other
    rw [Array.getElem_set_self (stored.valid channel), leaveGuards_count]
    simp
  · have addressDifferent : offset + channel.val ≠ offset + other.val := by
      intro equal
      have values : channel.val = other.val := by omega
      exact same (Fin.ext values.symm)
    rw [Array.getElem_set_ne (stored.valid channel) (stored.valid other) addressDifferent]
    rw [stored.held other, leaveGuards_count]
    simp [same, Ne.symm same]

end Controller.Cost.ForestCounter
