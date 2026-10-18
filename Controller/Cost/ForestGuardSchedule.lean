module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestCounterFrame

@[expose] public section

/-!
# Executed guard-operation schedules

A schedule retains every guard entry and exit occurrence. Each event executes
its five indexed counter instructions in a supplied program, preserving the
live traversal/output frame. This is the guard-operation component, not a
complete graph walker or weighted selector implementation.
-/
namespace Controller.Cost.ForestGuardSchedule

open Controller.Decoder Controller.Cost.GateProgram Controller.Cost.ForestCounter

inductive GuardEvent (n : ℕ) where
  | enter (channel : Channel n)
  | leave (channel : Channel n)
  deriving DecidableEq, Repr

namespace GuardEvent

def channel : GuardEvent n → Channel n
  | .enter coordinate | .leave coordinate => coordinate

def delta (width : ℕ) : GuardEvent n → ℕ
  | .enter _ => 1
  | .leave _ => 2 ^ width - 1

end GuardEvent

/-- The event trace of the same positional guarded traversal, without callbacks. -/
def walkEvents (graph : DAG n) (index : Fin graph.nodeCount) : List (GuardEvent n) :=
  match graph.node index with
  | .zero | .input _ | .liveAnd _ _ => []
  | .disj children => children.flatMap fun child => walkEvents graph (graph.childIndex index child)
  | .guard child labels =>
      labels.map GuardEvent.enter ++ walkEvents graph (graph.childIndex index child) ++
        labels.reverse.map GuardEvent.leave
termination_by index.val
decreasing_by all_goals exact graph.childIndex_lt _ _

/-- Roots are visited by position, so repeated terminal roots remain represented. -/
def rootEvents (graph : DAG n) : List (GuardEvent n) :=
  graph.roots.flatMap (walkEvents graph)

/-- There is no hidden channel-array reset between events or between roots. -/
def code (width offset : ℕ) : List (GuardEvent n) → List (Instruction width 4)
  | [] => []
  | event :: rest => changeCode width (offset + event.channel.val) (event.delta width) ++
      code width offset rest

theorem code_length (width offset : ℕ) (events : List (GuardEvent n)) :
    (code width offset events).length = 5 * events.length := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      simp only [code, List.length_append, changeCode_length, List.length_cons, ih]
      omega

def storedWord (heap : Array (Word width)) (address : ℕ) : Word width :=
  heap[address]?.getD (word width 0)

/-- The total specification leaves invalid addresses unchanged; execution is
claimed only with the explicit Valid hypothesis. -/
def update (width offset : ℕ) (heap : Array (Word width)) (event : GuardEvent n) :
    Array (Word width) :=
  let address := offset + event.channel.val
  if valid : address < heap.size then
    heap.set address (word width ((storedWord heap address).val + (word width (event.delta width)).val)) valid
  else heap

@[simp] theorem update_size (width offset : ℕ) (heap : Array (Word width))
    (event : GuardEvent n) : (update width offset heap event).size = heap.size := by
  by_cases valid : offset + event.channel.val < heap.size
  · simp [update, valid]
  · simp [update, valid]

/-- Address validity is a local invariant, not an executable scan over channels. -/
def Valid (width offset : ℕ) (heap : Array (Word width)) : List (GuardEvent n) → Prop
  | [] => True
  | event :: rest =>
      offset + event.channel.val < heap.size ∧ offset + event.channel.val < 2 ^ width ∧
        Valid width offset (update width offset heap event) rest

/-- Address validity follows from represented heap space and the actual event
addresses. The hypothesis is an invariant, not a channel initialization loop. -/
theorem valid_of_addresses (width offset : ℕ) (heap : Array (Word width))
    (events : List (GuardEvent n)) (represented : heap.size ≤ 2 ^ width)
    (addresses : ∀ event ∈ events, offset + event.channel.val < heap.size) :
    Valid width offset heap events := by
  induction events generalizing heap with
  | nil => trivial
  | cons event rest ih =>
      have current := addresses event (by simp)
      refine ⟨current, current.trans_le represented, ?_⟩
      apply ih (update width offset heap event)
      · simpa only [update_size] using represented
      · intro later membership
        simpa only [update_size] using addresses later (List.mem_cons_of_mem event membership)

/-- The actual boundary state after the represented schedule. -/
def finalState (width offset base : ℕ) (heap : Array (Word width))
    (oldAddress oldCounter oldIncrement : Word width) : List (GuardEvent n) → State width 4
  | [] => counterState heap base oldAddress oldCounter oldIncrement
  | event :: rest =>
      let address := offset + event.channel.val
      let counter := word width ((storedWord heap address).val + (word width (event.delta width)).val)
      finalState width offset (base + 5) (update width offset heap event)
        (word width address) counter (word width (event.delta width)) rest

theorem storedWord_eq (heap : Array (Word width)) (address : ℕ)
    (valid : address < heap.size) : storedWord heap address = heap[address] := by
  simp [storedWord, Array.getElem?_eq_getElem valid]

/-- Every event performs five genuine fetched transitions; all retained words
remain live. This theorem charges only the guard schedule. -/
theorem execution (program : Program width 4) (offset base : ℕ)
    (heap : Array (Word width)) (oldAddress oldCounter oldIncrement : Word width)
    (events : List (GuardEvent n)) (stack output : List (Word width))
    (fits : base + 5 * events.length < 2 ^ width)
    (valid : Valid width offset heap events)
    (block : BlockAt program base (code width offset events)) :
    Execution program ((counterState heap base oldAddress oldCounter oldIncrement).frame stack output)
      ((finalState width offset base heap oldAddress oldCounter oldIncrement events).frame stack output)
      (5 * events.length) (5 + heap.size + stack.length + output.length) := by
  induction events generalizing base heap oldAddress oldCounter oldIncrement with
  | nil =>
      simpa only [finalState, List.length_nil, Nat.mul_zero, framed_counterState_liveWords]
        using Execution.refl (p := program)
          ((counterState heap base oldAddress oldCounter oldIncrement).frame stack output)
  | cons event rest ih =>
      rcases valid with ⟨addressValid, addressFits, restValid⟩
      have head := BlockAt.prefix program base
        (changeCode width (offset + event.channel.val) (event.delta width))
        (code width offset rest) block
      have tail : BlockAt program (base + 5) (code width offset rest) := by
        simpa only [changeCode_length] using BlockAt.suffix program base
          (changeCode width (offset + event.channel.val) (event.delta width))
          (code width offset rest) block
      have first := change_execution_framed program heap base (offset + event.channel.val)
        (event.delta width) oldAddress oldCounter oldIncrement
        (storedWord heap (offset + event.channel.val)) stack output
        (by simp only [List.length_cons] at fits; omega) addressFits addressValid
        (storedWord_eq heap _ addressValid).symm head
      have restTrace := ih (base + 5) (update width offset heap event)
        (word width (offset + event.channel.val))
        (word width ((storedWord heap (offset + event.channel.val)).val +
          (word width (event.delta width)).val))
        (word width (event.delta width))
        (by simp only [List.length_cons] at fits; omega) restValid tail
      have joined := first.append (by simpa only [update, dite_eq_left addressValid] using restTrace)
      simpa only [finalState, update, dite_eq_left addressValid, List.length_cons,
        Nat.mul_add, Nat.mul_one, Nat.mul_succ, Nat.mul_zero, Nat.zero_add, Nat.add_zero,
        Array.size_set, Nat.max_self,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using joined

end Controller.Cost.ForestGuardSchedule
