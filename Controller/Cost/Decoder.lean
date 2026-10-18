module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Refinement
public import Controller.Decoder.Foundation

@[expose] public section

/-! Indexed storage refinement for decoder evaluation. The vector result
retains one Boolean entry per stored node, including shared nodes. Instruction
refinement and sparse cone initialization are separate obligations. -/
namespace Controller.Decoder.DAG

/-- Evaluate the first `length` nodes and store their values in a vector. -/
def evalVectorPrefix (graph : DAG n) (assignment : Assignment n) :
    (length : Nat) → length ≤ graph.nodeCount → Vector Bool length
  | 0, _ => #v[]
  | length + 1, bound =>
      let earlier := graph.evalVectorPrefix assignment length
        (Nat.le_trans (Nat.le_succ length) bound)
      let gate := graph.node ⟨length, Nat.lt_of_lt_of_le (Nat.lt_succ_self length) bound⟩
      earlier.push (gate.eval assignment (fun child => earlier[child.val]))

/-- The full stored table; each topological node is evaluated once. -/
def evalVector (graph : DAG n) (assignment : Assignment n) : Vector Bool graph.nodeCount :=
  graph.evalVectorPrefix assignment graph.nodeCount (Nat.le_refl _)

theorem evalVectorPrefix_eq_eval (graph : DAG n) (assignment : Assignment n) :
    ∀ (length : Nat) (bound : length ≤ graph.nodeCount) (index : Fin length),
      (graph.evalVectorPrefix assignment length bound)[index.val] =
        graph.eval assignment (index.castLE bound) := by
  intro length
  induction length with
  | zero => intro bound index; exact Fin.elim0 index
  | succ length ih =>
    intro bound index
    refine Fin.lastCases ?_ (fun earlierIndex => ?_) index
    · simp only [evalVectorPrefix, Fin.val_last, Vector.getElem_push_eq]
      rw [graph.eval_eq]
      apply Gate.eval_congr
      · intro channel _; rfl
      · intro child _; exact ih _ child
    · simp only [evalVectorPrefix, Fin.val_castSucc]
      rw [Vector.getElem_push_lt earlierIndex.isLt]
      simpa only [Fin.castLE, Fin.castSucc, Fin.castAdd] using
        ih (Nat.le_trans (Nat.le_succ length) bound) earlierIndex

theorem evalVector_eq_eval (graph : DAG n) (assignment : Assignment n)
    (index : Fin graph.nodeCount) :
    (graph.evalVector assignment)[index.val] = graph.eval assignment index := by
  exact graph.evalVectorPrefix_eq_eval assignment graph.nodeCount (Nat.le_refl _) index

end Controller.Decoder.DAG

namespace Controller.Cost

/-- A fragment trace records the actual fetched program-counter region.
The final state can leave the region, permitting a subsequent fragment. -/
inductive RegionExecution (program : Program width registers) (region : Finset Nat) :
    State width registers → State width registers → Nat → Nat → Prop where
  | refl (state) : RegionExecution program region state state 0 state.liveWords
  | cons {state middle final ticks peak}
      (inside : state.pc.val ∈ region)
      (transition : programStep program state = some middle)
      (rest : RegionExecution program region middle final ticks peak) :
      RegionExecution program region state final (ticks + 1) (max state.liveWords peak)

/-- The region annotation never replaces any machine transition. -/
theorem RegionExecution.execution {program : Program width registers} {region}
    {state final ticks peak} (trace : RegionExecution program region state final ticks peak) :
    Execution program state final ticks peak := by
  induction trace with
  | refl state => exact .refl state
  | cons _ transition _ inductionHypothesis => exact .cons transition inductionHypothesis

/-- A fragment can run inside a larger program when the actually fetched
instructions agree. No condition is imposed on the destination continuation. -/
theorem RegionExecution.replay {program destination : Program width registers} {region}
    {state final ticks peak} (trace : RegionExecution program region state final ticks peak)
    (agreement : ∀ address ∈ region, program[address]? = destination[address]?) :
    RegionExecution destination region state final ticks peak := by
  induction trace with
  | refl state => exact .refl state
  | @cons current middle final ticks peak inside transition rest inductionHypothesis =>
      refine .cons inside ?_ inductionHypothesis
      have same : programStep destination current = programStep program current := by
        unfold programStep
        rw [← agreement _ inside]
      rw [same]
      exact transition

/-- Boolean values occupy one word; decoding needs capacity for both 0 and 1. -/
def boolWord (width : Nat) (value : Bool) : Word width :=
  word width (if value then 1 else 0)

/-- Boolean encodings have their ordinary values when the word can store 1. -/
theorem boolWord_val (width : Nat) (capacity : 1 < 2 ^ width) (value : Bool) :
    (boolWord width value).val = if value then 1 else 0 := by
  cases value <;> simp [boolWord, word, Nat.mod_eq_of_lt, capacity, Nat.two_pow_pos]

/-- Testing the encoded word for zero agrees with Boolean falsity. -/
theorem boolWord_zero_iff (width : Nat) (capacity : 1 < 2 ^ width) (value : Bool) :
    (boolWord width value).val = 0 ↔ value = false := by
  rw [boolWord_val width capacity value]
  cases value <;> simp

/-- The fetched conditional jump follows the represented Boolean value.
This is the control primitive used to scan disjunctions and negative guards. -/
theorem branch_boolWord_execution (program : Program width registers)
    (state : State width registers) (source : Fin registers) (value : Bool)
    (target : Word width) (capacity : 1 < 2 ^ width)
    (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.branchZero source target))
    (held : state.reg source = boolWord width value) :
    Execution program state
      (if value = false then { state.advance with pc := target } else state.advance)
      1 state.liveWords := by
  have transition : programStep program state =
      some (if value = false then { state.advance with pc := target } else state.advance) := by
    unfold programStep
    rw [fetched]
    change step (.branchZero source target) state = _
    cases value <;> simp [step, running, held, boolWord_val width capacity]
  have trace := Execution.cons transition
    (Execution.refl (if value = false then { state.advance with pc := target } else state.advance))
  cases value <;> simpa [State.liveWords, State.advance] using trace

/-- A contiguous heap segment stores an indexed Boolean value table. -/
structure BoolTableStored (values : Vector Bool length) (offset : Nat)
    (heap : Array (Word width)) : Prop where
  fits : offset + length ≤ heap.size
  entry : ∀ index : Fin length,
    heap[offset + index.val]'(by omega) = boolWord width values[index.val]

/-- A fetched load reads the represented node value from the actual heap. -/
theorem load_boolTable (program : Program width registers) (state : State width registers)
    (values : Vector Bool length) (offset : Nat) (stored : BoolTableStored values offset state.heap)
    (index : Fin length) (destination address : Fin registers)
    (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.load destination address))
    (points : (state.reg address).val = offset + index.val) :
    programStep program state =
      some (state.advance.put destination (boolWord width values[index.val])) := by
  have valid : (state.reg address).val < state.heap.size := by
    have fits := stored.fits
    have indexBound := index.isLt
    omega
  unfold programStep
  rw [fetched]
  change step (.load destination address) state = _
  simp only [step, running, Bool.false_eq_true, ite_false, valid, dite_eq_left]
  have read : state.heap[(state.reg address).val] = boolWord width values[index.val] := by
    simpa only [points] using stored.entry index
  rw [read]

/-- This table read uses one actual fetched instruction and no extra storage. -/
theorem load_boolTable_execution (program : Program width registers)
    (state : State width registers) (values : Vector Bool length) (offset : Nat)
    (stored : BoolTableStored values offset state.heap) (index : Fin length)
    (destination address : Fin registers) (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.load destination address))
    (points : (state.reg address).val = offset + index.val) :
    Execution program state
      (state.advance.put destination (boolWord width values[index.val])) 1 state.liveWords := by
  have transition := load_boolTable program state values offset stored index destination address
    running fetched points
  have trace := Execution.cons transition
    (Execution.refl (state.advance.put destination (boolWord width values[index.val])))
  simpa [State.liveWords, State.advance, State.put] using trace

/-- Appending a node value extends the contiguous table and retains all
previous entries, including values shared by several later gates. -/
theorem BoolTableStored.push (values : Vector Bool length) (offset : Nat)
    (heap : Array (Word width)) (stored : BoolTableStored values offset heap)
    (atEnd : offset + length = heap.size) (value : Bool) :
    BoolTableStored (values.push value) offset (heap.push (boolWord width value)) := by
  have fit : offset + (length + 1) ≤ (heap.push (boolWord width value)).size := by
    simp only [Array.size_push]
    omega
  refine { fits := fit, entry := ?_ }
  intro index
  refine Fin.lastCases ?_ (fun earlier => ?_) index
  · simp only [Fin.val_last, Vector.getElem_push_eq]
    simpa only [atEnd] using (Array.getElem_push_eq (xs := heap) (x := boolWord width value))
  · simp only [Fin.val_castSucc, Vector.getElem_push_lt earlier.isLt]
    rw [Array.getElem_push_lt (by have := stored.fits; have := earlier.isLt; omega)]
    exact stored.entry earlier

/-- A fetched allocation instruction stores a computed Boolean node value. -/
theorem allocate_boolWord (program : Program width registers) (state : State width registers)
    (source : Fin registers) (value : Bool) (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.allocate source))
    (held : state.reg source = boolWord width value) (capacity : state.heap.size < 2 ^ width) :
    programStep program state =
      some { state.advance with heap := state.heap.push (boolWord width value) } := by
  unfold programStep
  rw [fetched]
  change step (.allocate source) state = _
  simp only [step, running, Bool.false_eq_true, ite_false, capacity, ite_true, held]

/-- The allocation uses one fetched instruction and adds exactly one live word. -/
theorem allocate_boolWord_execution (program : Program width registers)
    (state : State width registers) (source : Fin registers) (value : Bool)
    (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.allocate source))
    (held : state.reg source = boolWord width value) (capacity : state.heap.size < 2 ^ width) :
    Execution program state
      { state.advance with heap := state.heap.push (boolWord width value) }
      1 (state.liveWords + 1) := by
  have transition := allocate_boolWord program state source value running fetched held capacity
  have trace := Execution.cons transition
    (Execution.refl { state.advance with heap := state.heap.push (boolWord width value) })
  have newWords :
      ({ state.advance with heap := state.heap.push (boolWord width value) } : State width registers).liveWords =
        state.liveWords + 1 := by
    simp [State.liveWords, State.advance, Nat.add_assoc]
    omega
  simpa only [newWords, Nat.zero_add, Nat.max_eq_right (Nat.le_succ _)] using trace


/-- Loading a Boolean constant is one fetched instruction. -/
theorem constant_boolWord_execution (program : Program width registers)
    (state : State width registers) (destination : Fin registers) (value : Bool)
    (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.constant destination (boolWord width value))) :
    Execution program state
      (state.advance.put destination (boolWord width value)) 1 state.liveWords := by
  have transition : programStep program state =
      some (state.advance.put destination (boolWord width value)) := by
    unfold programStep
    rw [fetched]
    change step (.constant destination (boolWord width value)) state = _
    simp [step, running]
  have trace := Execution.cons transition
    (Execution.refl (state.advance.put destination (boolWord width value)))
  simpa [State.liveWords, State.advance, State.put] using trace

/-- Allocating the next computed node extends the represented value table.
The representation is tied to the actual allocation transition. -/
theorem allocate_boolTable (program : Program width registers)
    (state : State width registers) (values : Vector Bool length) (offset : Nat)
    (stored : BoolTableStored values offset state.heap)
    (atEnd : offset + length = state.heap.size) (source : Fin registers)
    (value : Bool) (running : state.halted = false)
    (fetched : program[state.pc.val]? = some (.allocate source))
    (held : state.reg source = boolWord width value)
    (capacity : state.heap.size < 2 ^ width) :
    ∃ next, programStep program state = some next ∧
      BoolTableStored (values.push value) offset next.heap ∧
      Execution program state next 1 (state.liveWords + 1) := by
  refine ⟨{ state.advance with heap := state.heap.push (boolWord width value) }, ?_, ?_, ?_⟩
  · exact allocate_boolWord program state source value running fetched held capacity
  · exact BoolTableStored.push values offset state.heap stored atEnd value
  · exact allocate_boolWord_execution program state source value running fetched held capacity

/-- A constant node is evaluated and appended by two actual fetched
instructions. Existing entries and shared references retain their values. -/
theorem constant_node_execution (program : Program width registers)
    (state : State width registers) (values : Vector Bool length) (offset : Nat)
    (stored : BoolTableStored values offset state.heap)
    (atEnd : offset + length = state.heap.size) (destination : Fin registers)
    (value : Bool) (running : state.halted = false)
    (first : program[state.pc.val]? = some (.constant destination (boolWord width value)))
    (second : program[state.advance.pc.val]? = some (.allocate destination))
    (capacity : state.heap.size < 2 ^ width) :
    ∃ next, BoolTableStored (values.push value) offset next.heap ∧
      Execution program state next 2 (state.liveWords + 1) := by
  let middle := state.advance.put destination (boolWord width value)
  have firstTrace := constant_boolWord_execution program state destination value running first
  have middleStored : BoolTableStored values offset middle.heap := by
    simpa [middle, State.advance, State.put] using stored
  have middleEnd : offset + length = middle.heap.size := by
    simpa [middle, State.advance, State.put] using atEnd
  have middleRunning : middle.halted = false := by
    simpa [middle, State.advance, State.put] using running
  have middleFetched : program[middle.pc.val]? = some (.allocate destination) := by
    simpa [middle, State.put] using second
  have middleHeld : middle.reg destination = boolWord width value := by
    simp [middle, State.put]
  have middleCapacity : middle.heap.size < 2 ^ width := by
    simpa [middle, State.advance, State.put] using capacity
  obtain ⟨next, _, nextStored, secondTrace⟩ := allocate_boolTable program middle values offset
    middleStored middleEnd destination value middleRunning middleFetched middleHeld middleCapacity
  refine ⟨next, nextStored, ?_⟩
  have combined := firstTrace.append secondTrace
  have middleWords : middle.liveWords = state.liveWords := by
    simp [middle, State.liveWords, State.advance, State.put]
  simpa [middle, middleWords, Nat.max_eq_right (Nat.le_succ state.liveWords)] using combined

/-- An input or shared-child node copies its stored Boolean value into the
next output entry using a load followed by allocation. -/
theorem copied_node_execution (program : Program width registers)
    (state : State width registers) (inputs : Vector Bool inputLength) (inputOffset : Nat)
    (inputStored : BoolTableStored inputs inputOffset state.heap)
    (index : Fin inputLength) (values : Vector Bool length) (offset : Nat)
    (stored : BoolTableStored values offset state.heap)
    (atEnd : offset + length = state.heap.size) (destination address : Fin registers)
    (running : state.halted = false)
    (first : program[state.pc.val]? = some (.load destination address))
    (points : (state.reg address).val = inputOffset + index.val)
    (second : program[state.advance.pc.val]? = some (.allocate destination))
    (capacity : state.heap.size < 2 ^ width) :
    ∃ next, BoolTableStored (values.push inputs[index.val]) offset next.heap ∧
      Execution program state next 2 (state.liveWords + 1) := by
  let middle := state.advance.put destination (boolWord width inputs[index.val])
  have firstTrace := load_boolTable_execution program state inputs inputOffset inputStored
    index destination address running first points
  have middleStored : BoolTableStored values offset middle.heap := by
    simpa [middle, State.advance, State.put] using stored
  have middleEnd : offset + length = middle.heap.size := by
    simpa [middle, State.advance, State.put] using atEnd
  have middleRunning : middle.halted = false := by
    simpa [middle, State.advance, State.put] using running
  have middleFetched : program[middle.pc.val]? = some (.allocate destination) := by
    simpa [middle, State.put] using second
  have middleHeld : middle.reg destination = boolWord width inputs[index.val] := by
    simp [middle, State.put]
  have middleCapacity : middle.heap.size < 2 ^ width := by
    simpa [middle, State.advance, State.put] using capacity
  obtain ⟨next, _, nextStored, secondTrace⟩ := allocate_boolTable program middle values offset
    middleStored middleEnd destination inputs[index.val] middleRunning middleFetched middleHeld middleCapacity
  refine ⟨next, nextStored, ?_⟩
  have combined := firstTrace.append secondTrace
  have middleWords : middle.liveWords = state.liveWords := by
    simp [middle, State.liveWords, State.advance, State.put]
  simpa [middle, middleWords, Nat.max_eq_right (Nat.le_succ state.liveWords)] using combined

end Controller.Cost
