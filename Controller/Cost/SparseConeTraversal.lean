module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SparseConeProgram
public import Controller.Decoder.Cone

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Fetched depth-first continuations over the retained physical DAG cache.
Node identities, child counts and cursors occupy charged machine words.
Completed nodes occupy a physical postorder ledger and supply original-ID
completion ranks. -/
namespace Controller.Cost.SparseConeTraversal
open Controller.Cost Controller.Cost.SparseConeProgram
open Controller.Decoder
variable {width n : Nat}

private theorem fetched (program : Program width 8) (state : State width 8)
    (entry : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (present : program[entry]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt fits, present]
  rfl

/-- A fresh DFS frame is entered from the actual source-ID word pushed by
first touch. Its node identity is retained below all subsequent continuations. -/
theorem enter_execution (program : Program width 8) (state : State width 8)
    (entry arityBase childDirectory identifier depth count cursor : Nat)
    (suffix : List (Word width))
    (present : ∀ phase : Fin 10, program[entry + phase.val]? =
      (enterCode width arityBase childDirectory)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 10 < 2 ^ width)
    (stack : state.stack = word width identifier :: suffix)
    (depthHeld : state.reg 7 = word width depth) (one : state.reg 3 = word width 1)
    (depthFits : depth + 1 < 2 ^ width)
    (arityFits : arityBase + 2 * identifier < 2 ^ width)
    (sourceFits : childDirectory + 2 * identifier < 2 ^ width)
    (arityBound : arityBase + 2 * identifier < state.heap.size)
    (sourceBound : childDirectory + 2 * identifier < state.heap.size)
    (arityCell : state.heap[arityBase + 2 * identifier]'arityBound = word width count)
    (sourceCell : state.heap[childDirectory + 2 * identifier]'sourceBound = word width cursor) :
    ∃ final, Execution program state final 10 state.liveWords ∧
      final.reg 0 = word width (2 * identifier) ∧ final.reg 7 = word width (depth + 1) ∧
      final.reg 4 = word width count ∧ final.reg 6 = word width cursor ∧
      final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 10) ∧ final.halted = false := by
  let s1 : State width 8 := { state.advance.put 0 (word width identifier) with stack := suffix }
  let s2 : State width 8 := { s1.advance with stack := word width identifier :: suffix }
  let s3 := s2.advance.put 7 (word width (depth + 1))
  let middle := s3.advance.put 0 (word width (2 * identifier))
  have idVal : (word width identifier).val = identifier := Nat.mod_eq_of_lt (by omega)
  have depthVal : (word width depth).val = depth := Nat.mod_eq_of_lt (by omega)
  have oneVal : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.put, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.put, State.advance, p1]
    rw [show (word width (entry + 1)).val = (entry + 1) from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = (entry + 2) from Nat.mod_eq_of_lt (by omega)]
  have p4 : middle.pc = word width (entry + 4) := by
    simp only [middle, State.put, State.advance, p3]
    rw [show (word width (entry + 3)).val = (entry + 3) from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.pop 0)
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [enterCode] using present ⟨0, by decide⟩)]
    simp [step, s1, s2, s3, middle, State.put, State.advance, running,
      stack, depthHeld, depthVal, one, oneVal, idVal, two_mul]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.push 0)
      (by simpa only [Nat.add_zero] using p1) (by omega)
      (by simpa [enterCode] using present ⟨1, by decide⟩)]
    simp [step, s1, s2, s3, middle, State.put, State.advance, running,
      stack, depthHeld, depthVal, one, oneVal, idVal, two_mul]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.add 7 7 3)
      (by simpa only [Nat.add_zero] using p2) (by omega)
      (by simpa [enterCode] using present ⟨2, by decide⟩)]
    simp [step, s1, s2, s3, middle, State.put, State.advance, running,
      stack, depthHeld, depthVal, one, oneVal, idVal, two_mul]
  have t3 : programStep program s3 = some middle := by
    rw [fetched program s3 (entry + 3) (.add 0 0 0)
      (by simpa only [Nat.add_zero] using p3) (by omega)
      (by simpa [enterCode] using present ⟨3, by decide⟩)]
    simp [step, s1, s2, s3, middle, State.put, State.advance, running,
      stack, depthHeld, depthVal, one, oneVal, idVal, two_mul]
  have middleLive : middle.liveWords = state.liveWords := by
    simp [middle, s3, s2, s1, State.liveWords, State.advance, State.put, stack]
  have s1Bound : s1.liveWords ≤ state.liveWords := by
    simp [s1, State.liveWords, State.advance, State.put, stack] <;> omega
  have first : Execution program state middle 4 state.liveWords := by
    have trace := Execution.cons t0 (Execution.cons t1
      (Execution.cons t2 (Execution.cons t3 (Execution.refl middle))))
    simpa only [middleLive, show s2.liveWords = state.liveWords from by
        simp [s2, s1, State.liveWords, State.advance, State.put, stack],
      show s3.liveWords = state.liveWords from by
        simp [s3, s2, s1, State.liveWords, State.advance, State.put, stack],
      Nat.max_self, Nat.max_eq_right s1Bound] using trace
  have directoryAt : ∀ phase : Fin 6, program[(entry + 4) + phase.val]? =
      (directoryCode width arityBase childDirectory)[phase.val]? := by
    intro phase
    have cell := present ⟨4 + phase.val, by have := phase.isLt <;> omega⟩
    fin_cases phase <;> simpa [enterCode, directoryCode, Nat.add_assoc] using cell
  obtain ⟨final, last, countHeld, cursorHeld, offsetFinal, zeroFinal, oneFinal,
      depthFinal, heap, caller, output, pc, halted⟩ :=
    directory_execution program middle (entry + 4) (2 * identifier) arityBase childDirectory count cursor
      directoryAt p4 (by simp [middle, s3, s2, s1, State.advance, State.put, running])
      (by omega) (by simp [middle, State.put]) arityFits sourceFits
      (by simpa [middle, s3, s2, s1, State.advance, State.put] using arityBound)
      (by simpa [middle, s3, s2, s1, State.advance, State.put] using sourceBound)
      (by simpa [middle, s3, s2, s1, State.advance, State.put] using arityCell)
      (by simpa [middle, s3, s2, s1, State.advance, State.put] using sourceCell)
  refine ⟨final, ?_, ?_, ?_, countHeld, cursorHeld, ?_, ?_, ?_, ?_, ?_, ?_, halted⟩
  · simpa only [middleLive, Nat.max_self, Nat.reduceAdd] using first.append last
  · simpa [middle, State.put] using offsetFinal
  · simpa [middle, s3, State.advance, State.put] using depthFinal
  · simpa [middle, s3, s2, s1, State.advance, State.put] using zeroFinal
  · simpa [middle, s3, s2, s1, State.advance, State.put] using oneFinal
  · simpa [middle, s3, s2, s1, State.advance, State.put] using heap
  · simpa [middle, s3, s2, s1, State.advance, State.put, stack] using caller
  · simpa [middle, s3, s2, s1, State.advance, State.put] using output
  · simpa [Nat.add_assoc] using pc

/-- The active DFS spine stores original node identities. Each child is
entered immediately; discovered nodes outside this spine are completed. -/
structure DFSState (graph : Controller.Decoder.DAG n) where
  completed : List (Fin graph.nodeCount)
  active : List (Fin graph.nodeCount)
  completedUnique : completed.Nodup
  activeUnique : active.Nodup
  separate : List.Disjoint completed active
  closed : ∀ node ∈ completed, ∀ child ∈ (graph.node node).children,
    graph.childIndex node child ∈ completed

/-- An entered node sees only strictly larger active ancestors. -/
def AncestorsAbove (graph : Controller.Decoder.DAG n)
    (current : Fin graph.nodeCount) (active : List (Fin graph.nodeCount)) : Prop :=
  ∀ ancestor ∈ active, current.val < ancestor.val

/-- Row/phase continuations carry counts and physical cursors. The runtime
stack words, including caller suffix, are part of the invariant. -/
structure Continuation (width : Nat) where
  remaining : Nat
  cursor : Nat
  node : Nat

def continuationWords (width : Nat) (frame : Continuation width) : List (Word width) :=
  [word width frame.cursor, word width frame.remaining, word width frame.node]

/-- Charging excludes declared ambient channels. They belong to the shared
initialized layout; each query charges only original retained incidences. -/
def localNodeWeight (graph : Controller.Decoder.DAG n)
    (node : Fin graph.nodeCount) : Nat :=
  1 + (graph.node node).children.length + (graph.node node).guardLabels.length +
    (graph.node node).directChannels.length

private theorem decrement (remaining : Nat) (fits : remaining + 1 < 2 ^ width) :
    word width ((word width (remaining + 1)).val + (word width (2 ^ width - 1)).val) =
      word width remaining := by
  rw [show (word width (remaining + 1)).val = remaining + 1 from Nat.mod_eq_of_lt fits,
    show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from
      Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width <;> omega)]
  have sum : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by
    have := Nat.two_pow_pos width <;> omega
  rw [sum]
  simp only [word, Nat.add_mod_left]

/-- Returning from a completed child restores the physical parent's cursor
and count, consumes exactly one original occurrence, and takes the backedge. -/
theorem resume_execution (program : Program width 8) (state : State width 8)
    (entry loop cursor remaining : Nat) (suffix : List (Word width))
    (present : ∀ phase : Fin 6, program[entry + phase.val]? =
      (resumeCode width loop)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 6 < 2 ^ width) (loopFits : loop < 2 ^ width)
    (stack : state.stack = word width cursor :: word width (remaining + 1) :: suffix)
    (zero : state.reg 2 = word width 0) (one : state.reg 3 = word width 1)
    (cursorFits : cursor + 1 < 2 ^ width) (countFits : remaining + 1 < 2 ^ width) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 0 = state.reg 0 ∧ final.reg 2 = state.reg 2 ∧
      final.reg 3 = state.reg 3 ∧ final.reg 7 = state.reg 7 ∧
      final.heap = state.heap ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width loop ∧ final.halted = false := by
  let s1 : State width 8 := { state.advance.put 6 (word width cursor) with
    stack := word width (remaining + 1) :: suffix }
  let s2 : State width 8 := { s1.advance.put 4 (word width (remaining + 1)) with stack := suffix }
  let s3 := s2.advance.put 5 (word width (2 ^ width - 1))
  let s4 := s3.advance.put 4 (word width remaining)
  let s5 := s4.advance.put 6 (word width (cursor + 1))
  let final : State width 8 := { s5.advance with pc := word width loop }
  have cursorVal : (word width cursor).val = cursor := Nat.mod_eq_of_lt (by omega)
  have oneVal : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have zeroVal : (word width 0).val = 0 := by simp [word]
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.put, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.put, State.advance, p1]
    rw [show (word width (entry + 1)).val = (entry + 1) from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = (entry + 2) from Nat.mod_eq_of_lt (by omega)]
  have p4 : s4.pc = word width (entry + 4) := by
    simp only [s4, State.put, State.advance, p3]
    rw [show (word width (entry + 3)).val = (entry + 3) from Nat.mod_eq_of_lt (by omega)]
  have p5 : s5.pc = word width (entry + 5) := by
    simp only [s5, State.put, State.advance, p4]
    rw [show (word width (entry + 4)).val = (entry + 4) from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.pop 6)
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [resumeCode] using present ⟨0, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, stack, zero, one, zeroVal, oneVal, cursorVal, decrement remaining countFits]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.pop 4)
      (by simpa only [Nat.add_zero] using p1) (by omega)
      (by simpa [resumeCode] using present ⟨1, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, stack, zero, one, zeroVal, oneVal, cursorVal, decrement remaining countFits]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.constant 5 (word width (2 ^ width - 1)))
      (by simpa only [Nat.add_zero] using p2) (by omega)
      (by simpa [resumeCode] using present ⟨2, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, stack, zero, one, zeroVal, oneVal, cursorVal, decrement remaining countFits]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.add 4 4 5)
      (by simpa only [Nat.add_zero] using p3) (by omega)
      (by simpa [resumeCode] using present ⟨3, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, stack, zero, one, zeroVal, oneVal, cursorVal, decrement remaining countFits]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 6 6 3)
      (by simpa only [Nat.add_zero] using p4) (by omega)
      (by simpa [resumeCode] using present ⟨4, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, stack, zero, one, zeroVal, oneVal, cursorVal, decrement remaining countFits]
  have t5 : programStep program s5 = some final := by
    rw [fetched program s5 (entry + 5) (.branchZero 2 (word width loop))
      (by simpa only [Nat.add_zero] using p5) (by omega)
      (by simpa [resumeCode] using present ⟨5, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, stack, zero, one, zeroVal, oneVal, cursorVal, decrement remaining countFits]
  have firstLe : s1.liveWords ≤ state.liveWords := by
    simp [s1, State.liveWords, State.advance, State.put, stack] <;> omega
  have secondLe : s2.liveWords ≤ s1.liveWords := by
    simp [s2, s1, State.liveWords, State.advance, State.put] <;> omega
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
      (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl final))))))
    simpa only [show s3.liveWords = s2.liveWords from rfl,
      show s4.liveWords = s2.liveWords from rfl, show s5.liveWords = s2.liveWords from rfl,
      show final.liveWords = s2.liveWords from rfl, Nat.max_self,
      Nat.max_eq_left secondLe, Nat.max_eq_left firstLe] using trace
  all_goals simp [final, s5, s4, s3, s2, s1, State.advance, State.put]

/-- The parent's physical cursor/count are charged suspension words, retained
below the fresh child word throughout the recursive descent. -/
theorem suspend_execution (program : Program width 8) (state : State width 8)
    (entry : Nat)
    (present : ∀ phase : Fin 2, program[entry + phase.val]? = (suspendCode)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 2 < 2 ^ width) :
    ∃ final, Execution program state final 2 (state.liveWords + 2) ∧
      final.reg = state.reg ∧ final.heap = state.heap ∧
      final.stack = state.reg 6 :: state.reg 4 :: state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 2) ∧ final.halted = false := by
  let middle : State width 8 := { state.advance with stack := state.reg 4 :: state.stack }
  let final : State width 8 := { middle.advance with stack := state.reg 6 :: middle.stack }
  have middlePC : middle.pc = word width (entry + 1) := by
    simp only [middle, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have finalPC : final.pc = word width (entry + 2) := by
    simp only [final, State.advance, middlePC]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some middle := by
    rw [fetched program state entry (.push 4) position (by omega)
      (by simpa [suspendCode] using present ⟨0, by decide⟩)]
    simp [step, middle, running]
  have t1 : programStep program middle = some final := by
    rw [fetched program middle (entry + 1) (.push 6) middlePC (by omega)
      (by simpa [suspendCode] using present ⟨1, by decide⟩)]
    simp [step, middle, final, State.advance, running]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, finalPC, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.refl final))
    have midLive : middle.liveWords = state.liveWords + 1 := by
      simp [middle, State.liveWords, State.advance] <;> omega
    have finalLive : final.liveWords = state.liveWords + 2 := by
      simp [final, middle, State.liveWords, State.advance] <;> omega
    simpa only [midLive, finalLive, Nat.max_eq_right (by omega : state.liveWords + 1 ≤ state.liveWords + 2),
      Nat.max_eq_right (by omega : state.liveWords ≤ state.liveWords + 2)] using trace

/-- Dispatch reads the marker result retained by the actual touch path. -/
theorem dispatch_fresh (program : Program width 8) (state : State width 8)
    (entry enter : Nat)
    (present : program[entry]? = some (.branchZero 5 (word width enter)))
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry < 2 ^ width) (fresh : state.reg 5 = word width 0) :
    Execution program state { state.advance with pc := word width enter } 1 state.liveWords := by
  have first : programStep program state = some { state.advance with pc := word width enter } := by
    rw [fetched program state entry (.branchZero 5 (word width enter)) position codeFits present]
    simp [step, running, fresh, word]
  simpa only [show ({ state.advance with pc := word width enter } : State width 8).liveWords = state.liveWords from rfl,
    Nat.max_self] using Execution.cons first (Execution.refl _)

theorem dispatch_stale (program : Program width 8) (state : State width 8)
    (entry enter resume : Nat)
    (present0 : program[entry]? = some (.branchZero 5 (word width enter)))
    (present1 : program[entry + 1]? = some (.branchZero 2 (word width resume)))
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 2 < 2 ^ width) (stale : (state.reg 5).val ≠ 0)
    (zero : state.reg 2 = word width 0) :
    Execution program state { state.advance.advance with pc := word width resume } 2 state.liveWords := by
  have first : programStep program state = some state.advance := by
    rw [fetched program state entry (.branchZero 5 (word width enter)) position (by omega) present0]
    simp [step, running, stale]
  have midPC : state.advance.pc = word width (entry + 1) := by
    simp only [State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have last : programStep program state.advance = some { state.advance.advance with pc := word width resume } := by
    rw [fetched program state.advance (entry + 1) (.branchZero 2 (word width resume)) midPC (by omega) present1]
    simp [step, State.advance, running, zero, word]
  simpa only [show state.advance.liveWords = state.liveWords from rfl,
    show ({ state.advance.advance with pc := word width resume } : State width 8).liveWords = state.liveWords from rfl,
    Nat.max_self] using Execution.cons first (Execution.cons last (Execution.refl _))

/-- One duplicate child occurrence is loaded, tested and skipped on the same
parent continuation. Its original physical cursor advances exactly once. -/
theorem child_stale_execution (program : Program width 8) (state : State width 8)
    (entry enter resume loop markerBase cursor identifier remaining : Nat) (flag : Word width)
    (suspendAt : ∀ phase : Fin 2, program[entry + phase.val]? = suspendCode[phase.val]?)
    (touchAt : TouchAt program markerBase (entry + 2))
    (dispatch0 : program[entry + 10]? = some (.branchZero 5 (word width enter)))
    (dispatch1 : program[entry + 11]? = some (.branchZero 2 (word width resume)))
    (resumeAt : ∀ phase : Fin 6, program[resume + phase.val]? = (resumeCode width loop)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 12 < 2 ^ width) (resumeFits : resume + 6 < 2 ^ width)
    (loopFits : loop < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countFits : remaining + 1 < 2 ^ width)
    (cursorHeld : state.reg 6 = word width cursor) (countHeld : state.reg 4 = word width (remaining + 1))
    (zero : state.reg 2 = word width 0) (one : state.reg 3 = word width 1)
    (sourceBound : cursor < state.heap.size)
    (source : state.heap[cursor]'sourceBound = word width identifier)
    (markerFits : markerBase + identifier < 2 ^ width)
    (markerBound : markerBase + identifier < state.heap.size)
    (marked : state.heap[markerBase + identifier]'markerBound = flag) (nonzero : flag.val ≠ 0) :
    ∃ final, Execution program state final 16 (state.liveWords + 2) ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧ final.reg 7 = state.reg 7 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width loop ∧ final.halted = false := by
  obtain ⟨suspended, first, regs, heap, stack, output, pc, halted⟩ :=
    suspend_execution program state entry suspendAt position running (by omega)
  have suspendedLive : suspended.liveWords = state.liveWords + 2 := by
    simp only [State.liveWords, heap, stack, output, List.length_cons] <;> omega
  obtain ⟨touched, second, touchHeap, touchStack, touchOutput, touchPC, touchRunning,
      cursorPreserved, zeroPreserved, onePreserved, countPreserved, depthPreserved, touchFlag⟩ :=
    touch_stale program suspended markerBase (entry + 2) cursor identifier touchAt pc halted
      (by omega) (by simpa only [regs] using cursorHeld) (by omega)
      (by simpa only [heap] using sourceBound) (by simpa only [heap] using source)
      markerFits (by simpa only [heap] using markerBound) flag
      (by simpa only [heap] using marked) nonzero (by simpa only [regs] using zero)
  let dispatched : State width 8 := { touched.advance.advance with pc := word width resume }
  have third : Execution program touched dispatched 2 touched.liveWords :=
    dispatch_stale program touched (entry + 10) enter resume dispatch0
      (by simpa only [Nat.add_assoc] using dispatch1)
      (by simpa only [Nat.add_assoc] using touchPC) touchRunning (by omega)
      (by rw [touchFlag]; exact nonzero)
      (by rw [zeroPreserved, regs]; exact zero)
  have dispatchedStack : dispatched.stack = word width cursor :: word width (remaining + 1) :: state.stack := by
    simp only [dispatched, State.advance, touchStack, stack, regs, cursorHeld, countHeld]
  obtain ⟨final, fourth, finalCount, finalCursor, _, finalZero, finalOne,
      finalDepth, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    resume_execution program dispatched resume loop cursor remaining state.stack resumeAt rfl
      (by simpa only [dispatched, State.advance] using touchRunning) resumeFits loopFits
      dispatchedStack (by simpa only [dispatched, State.advance, zeroPreserved, regs] using zero)
      (by simpa only [dispatched, State.advance, onePreserved, regs] using one) cursorFits countFits
  have touchedLive : touched.liveWords = state.liveWords + 2 := by
    simp only [State.liveWords, touchHeap, touchStack, touchOutput,
      heap, stack, output, List.length_cons] <;> omega
  have dispatchedLive : dispatched.liveWords = state.liveWords + 2 := touchedLive
  refine ⟨final, ?_, finalCount, finalCursor, ?_, ?_, ?_, ?_, finalStack, ?_, finalPC, finalRunning⟩
  · have trace := ((first.append second).append third).append fourth
    simpa only [suspendedLive, touchedLive, dispatchedLive, Nat.max_self, Nat.reduceAdd] using trace
  · simpa only [dispatched, State.advance, zeroPreserved, regs] using finalZero
  · simpa only [dispatched, State.advance, onePreserved, regs] using finalOne
  · simpa only [dispatched, State.advance, depthPreserved, regs] using finalDepth
  · simpa only [dispatched, State.advance, touchHeap, heap] using finalHeap
  · simpa only [dispatched, State.advance, touchOutput, output] using finalOutput

/-- Completion records the original node identity in postorder and publishes
its sparse rank only after the physical child traversal has returned. -/
def finishLedgerCode (width countSlot mapBase ledgerBase : Nat) : Program width 8 := #[
  .pop 0, .push 0,
  .constant 1 (word width countSlot), .load 5 1,
  .constant 1 (word width mapBase), .add 1 1 0, .store 1 5,
  .constant 1 (word width ledgerBase), .add 1 1 5, .store 1 0,
  .constant 1 (word width countSlot), .add 5 5 3, .store 1 5]

/-- A lower child cannot be one of the active ancestors. A marked child is
therefore already completed and has a usable physical map entry. -/
theorem marked_child_completed (graph : DAG n) (current : Fin graph.nodeCount)
    (child : Fin current.val) (completed ancestors : List (Fin graph.nodeCount))
    (above : AncestorsAbove graph current ancestors)
    (seen : graph.childIndex current child ∈ completed ∨
      graph.childIndex current child ∈ current :: ancestors) :
    graph.childIndex current child ∈ completed := by
  rcases seen with finished | active
  · exact finished
  · have earlier := graph.childIndex_lt current child
    rcases List.mem_cons.mp active with same | ancestor
    · have equalValues := congrArg Fin.val same
      omega
    · have later := above _ ancestor
      omega

/-- The terminal discovered set is the exact source cone once all pending
frames have completed; no source node outside the cone is admitted. -/
theorem completed_eq_cone (graph : DAG n) (root : Fin graph.nodeCount)
    (completed : List (Fin graph.nodeCount))
    (rootPresent : root ∈ completed)
    (closed : ∀ node ∈ completed, ∀ child ∈ (graph.node node).children,
      graph.childIndex node child ∈ completed)
    (inside : ∀ node ∈ completed, node ∈ graph.cone root) :
    completed.toFinset = graph.cone root := by
  apply Finset.Subset.antisymm
  · intro node member
    exact inside node (List.mem_toFinset.mp member)
  · apply graph.cone_subset_of_childClosed completed.toFinset _ root
    · exact List.mem_toFinset.mpr rootPresent
    · intro node member child childMember
      exact List.mem_toFinset.mpr (closed node (List.mem_toFinset.mp member) child
        (by simpa using childMember))

/-- Publish one completed original node without allocation or clearing the
retained source cache. The ledger rank is the actual stored completion count. -/
theorem finishLedger_execution (program : Program width 8) (state : State width 8)
    (entry countSlot mapBase ledgerBase identifier rank : Nat)
    (suffix : List (Word width))
    (present : ∀ phase : Fin 13, program[entry + phase.val]? =
      (finishLedgerCode width countSlot mapBase ledgerBase)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 13 < 2 ^ width)
    (stack : state.stack = word width identifier :: suffix)
    (one : state.reg 3 = word width 1)
    (countFits : countSlot < 2 ^ width)
    (mapFits : mapBase + identifier < 2 ^ width)
    (ledgerFits : ledgerBase + rank < 2 ^ width)
    (rankFits : rank + 1 < 2 ^ width)
    (countBound : countSlot < state.heap.size)
    (mapBound : mapBase + identifier < state.heap.size)
    (ledgerBound : ledgerBase + rank < state.heap.size)
    (countCell : state.heap[countSlot]'countBound = word width rank) :
    ∃ final, Execution program state final 13 state.liveWords ∧
      final.heap = ((state.heap.set (mapBase + identifier) (word width rank) mapBound).set
        (ledgerBase + rank) (word width identifier) (by simpa using ledgerBound)).set
          countSlot (word width (rank + 1)) (by simpa using countBound) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width identifier ∧ final.reg 5 = word width (rank + 1) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 5 →
        final.reg register = state.reg register) ∧
      final.pc = word width (entry + 13) ∧ final.halted = false := by
  let s1 : State width 8 := { state.advance.put 0 (word width identifier) with stack := suffix }
  let s2 : State width 8 := { s1.advance with stack := word width identifier :: suffix }
  let s3 : State width 8 := s2.advance.put 1 (word width countSlot)
  let s4 : State width 8 := s3.advance.put 5 (word width rank)
  let s5 : State width 8 := s4.advance.put 1 (word width mapBase)
  let s6 : State width 8 := s5.advance.put 1 (word width (mapBase + identifier))
  let s7 : State width 8 := { s6.advance with heap := state.heap.set (mapBase + identifier) (word width rank) }
  let s8 : State width 8 := s7.advance.put 1 (word width ledgerBase)
  let s9 : State width 8 := s8.advance.put 1 (word width (ledgerBase + rank))
  let s10 : State width 8 := { s9.advance with heap := s9.heap.set (ledgerBase + rank) (word width identifier) (by simpa [s9, s8, s7, State.put, State.advance] using ledgerBound) }
  let s11 : State width 8 := s10.advance.put 1 (word width countSlot)
  let s12 : State width 8 := s11.advance.put 5 (word width (rank + 1))
  let s13 : State width 8 := { s12.advance with heap := s12.heap.set countSlot (word width (rank + 1)) (by simpa [s12, s11, s10, s9, s8, s7, State.put, State.advance] using countBound) }
  have idFits : identifier < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have mapBaseFits : mapBase < 2 ^ width := by omega
  have ledgerBaseFits : ledgerBase < 2 ^ width := by omega
  have rankBaseFits : rank < 2 ^ width := by omega
  have countVal : (word width (countSlot)).val = countSlot := Nat.mod_eq_of_lt countFits
  have idVal : (word width (identifier)).val = identifier := Nat.mod_eq_of_lt idFits
  have mapBaseVal : (word width (mapBase)).val = mapBase := Nat.mod_eq_of_lt mapBaseFits
  have mapVal : (word width (mapBase + identifier)).val = mapBase + identifier := Nat.mod_eq_of_lt mapFits
  have ledgerBaseVal : (word width (ledgerBase)).val = ledgerBase := Nat.mod_eq_of_lt ledgerBaseFits
  have ledgerVal : (word width (ledgerBase + rank)).val = ledgerBase + rank := Nat.mod_eq_of_lt ledgerFits
  have rankVal : (word width (rank)).val = rank := Nat.mod_eq_of_lt rankBaseFits
  have oneVal : (word width (1)).val = 1 := Nat.mod_eq_of_lt oneFits
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.put, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.pop 0)
      (by simpa using position) (by omega)
      (by simpa [finishLedgerCode] using present ⟨0, by decide⟩)]
    simp [step, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.put, State.advance, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.push 0)
      (by simpa using p1) (by omega)
      (by simpa [finishLedgerCode] using present ⟨1, by decide⟩)]
    simp [step, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.constant 1 (word width countSlot))
      (by simpa using p2) (by omega)
      (by simpa [finishLedgerCode] using present ⟨2, by decide⟩)]
    simp [step, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p4 : s4.pc = word width (entry + 4) := by
    simp only [s4, State.put, State.advance, p3]
    rw [show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (by omega)]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.load 5 1)
      (by simpa using p3) (by omega)
      (by simpa [finishLedgerCode] using present ⟨3, by decide⟩)]
    simp [step, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p5 : s5.pc = word width (entry + 5) := by
    simp only [s5, State.put, State.advance, p4]
    rw [show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (by omega)]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.constant 1 (word width mapBase))
      (by simpa using p4) (by omega)
      (by simpa [finishLedgerCode] using present ⟨4, by decide⟩)]
    simp [step, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p6 : s6.pc = word width (entry + 6) := by
    simp only [s6, State.put, State.advance, p5]
    rw [show (word width (entry + 5)).val = entry + 5 from Nat.mod_eq_of_lt (by omega)]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.add 1 1 0)
      (by simpa using p5) (by omega)
      (by simpa [finishLedgerCode] using present ⟨5, by decide⟩)]
    simp [step, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p7 : s7.pc = word width (entry + 7) := by
    simp only [s7, State.put, State.advance, p6]
    rw [show (word width (entry + 6)).val = entry + 6 from Nat.mod_eq_of_lt (by omega)]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 6) (.store 1 5)
      (by simpa using p6) (by omega)
      (by simpa [finishLedgerCode] using present ⟨6, by decide⟩)]
    simp [step, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p8 : s8.pc = word width (entry + 8) := by
    simp only [s8, State.put, State.advance, p7]
    rw [show (word width (entry + 7)).val = entry + 7 from Nat.mod_eq_of_lt (by omega)]
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (entry + 7) (.constant 1 (word width ledgerBase))
      (by simpa using p7) (by omega)
      (by simpa [finishLedgerCode] using present ⟨7, by decide⟩)]
    simp [step, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p9 : s9.pc = word width (entry + 9) := by
    simp only [s9, State.put, State.advance, p8]
    rw [show (word width (entry + 8)).val = entry + 8 from Nat.mod_eq_of_lt (by omega)]
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (entry + 8) (.add 1 1 5)
      (by simpa using p8) (by omega)
      (by simpa [finishLedgerCode] using present ⟨8, by decide⟩)]
    simp [step, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p10 : s10.pc = word width (entry + 10) := by
    simp only [s10, State.put, State.advance, p9]
    rw [show (word width (entry + 9)).val = entry + 9 from Nat.mod_eq_of_lt (by omega)]
  have t9 : programStep program s9 = some s10 := by
    rw [fetched program s9 (entry + 9) (.store 1 0)
      (by simpa using p9) (by omega)
      (by simpa [finishLedgerCode] using present ⟨9, by decide⟩)]
    simp [step, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p11 : s11.pc = word width (entry + 11) := by
    simp only [s11, State.put, State.advance, p10]
    rw [show (word width (entry + 10)).val = entry + 10 from Nat.mod_eq_of_lt (by omega)]
  have t10 : programStep program s10 = some s11 := by
    rw [fetched program s10 (entry + 10) (.constant 1 (word width countSlot))
      (by simpa using p10) (by omega)
      (by simpa [finishLedgerCode] using present ⟨10, by decide⟩)]
    simp [step, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p12 : s12.pc = word width (entry + 12) := by
    simp only [s12, State.put, State.advance, p11]
    rw [show (word width (entry + 11)).val = entry + 11 from Nat.mod_eq_of_lt (by omega)]
  have t11 : programStep program s11 = some s12 := by
    rw [fetched program s11 (entry + 11) (.add 5 5 3)
      (by simpa using p11) (by omega)
      (by simpa [finishLedgerCode] using present ⟨11, by decide⟩)]
    simp [step, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  have p13 : s13.pc = word width (entry + 13) := by
    simp only [s13, State.put, State.advance, p12]
    rw [show (word width (entry + 12)).val = entry + 12 from Nat.mod_eq_of_lt (by omega)]
  have t12 : programStep program s12 = some s13 := by
    rw [fetched program s12 (entry + 12) (.store 1 5)
      (by simpa using p12) (by omega)
      (by simpa [finishLedgerCode] using present ⟨12, by decide⟩)]
    simp [step, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, mapBaseVal,
      mapVal, ledgerBaseVal, ledgerVal,
      rankVal, oneVal, countBound, mapBound, ledgerBound]
  refine ⟨s13, ?_, rfl, ?_, rfl, ?_, ?_, ?_, p13, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.refl s13)))))))))))))
    have live1 : s1.liveWords ≤ state.liveWords := by
      simp [s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live2 : s2.liveWords = state.liveWords := by
      simp [s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live3 : s3.liveWords = state.liveWords := by
      simp [s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live4 : s4.liveWords = state.liveWords := by
      simp [s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live5 : s5.liveWords = state.liveWords := by
      simp [s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live6 : s6.liveWords = state.liveWords := by
      simp [s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live7 : s7.liveWords = state.liveWords := by
      simp [s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live8 : s8.liveWords = state.liveWords := by
      simp [s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live9 : s9.liveWords = state.liveWords := by
      simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live10 : s10.liveWords = state.liveWords := by
      simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live11 : s11.liveWords = state.liveWords := by
      simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live12 : s12.liveWords = state.liveWords := by
      simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live13 : s13.liveWords = state.liveWords := by
      simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    simpa only [live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, Nat.max_self, Nat.max_eq_right live1] using trace
  · simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, stack]
  · simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]
  · simp [s13, s12, s11, State.advance, State.put]
  · intro register notZero notOne notFive
    simp [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      State.advance, State.put, notZero, notOne, notFive]

def widenRegister (register : Fin 4) : Fin 8 := register.castLE (by decide)

def widenInstruction : Instruction width 4 → Instruction width 8
  | .constant dst value => .constant (widenRegister dst) value
  | .copy dst src => .copy (widenRegister dst) (widenRegister src)
  | .add dst left right => .add (widenRegister dst) (widenRegister left) (widenRegister right)
  | .xor dst left right => .xor (widenRegister dst) (widenRegister left) (widenRegister right)
  | .load dst address => .load (widenRegister dst) (widenRegister address)
  | .store address src => .store (widenRegister address) (widenRegister src)
  | .allocate src => .allocate (widenRegister src)
  | .release => .release
  | .push src => .push (widenRegister src)
  | .pop dst => .pop (widenRegister dst)
  | .emit src => .emit (widenRegister src)
  | .branchZero src target => .branchZero (widenRegister src) target
  | .halt => .halt

def widenState (state : State width 4) (saved : Fin 8 → Word width) : State width 8 :=
  { reg := fun register => if small : register.val < 4 then
      state.reg ⟨register.val, small⟩ else saved register
    heap := state.heap, stack := state.stack, output := state.output,
    pc := state.pc, halted := state.halted }

@[simp] theorem widenState_low (state : State width 4) (saved : Fin 8 → Word width)
    (register : Fin 4) : (widenState state saved).reg (widenRegister register) = state.reg register := by
  simp [widenState, widenRegister]

@[simp] theorem widenState_high (state : State width 4) (saved : Fin 8 → Word width)
    (register : Fin 8) (large : 4 ≤ register.val) :
    (widenState state saved).reg register = saved register := by
  simp [widenState, show ¬register.val < 4 from by omega]

@[simp] theorem widenState_liveWords (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).liveWords = state.liveWords + 4 := by
  simp [widenState, State.liveWords]; omega

@[simp] theorem widenState_advance (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).advance = widenState state.advance saved := rfl

@[simp] theorem widenState_put (state : State width 4) (saved : Fin 8 → Word width)
    (dst : Fin 4) (value : Word width) :
    (widenState state saved).put (widenRegister dst) value =
      widenState (state.put dst value) saved := by
  unfold widenState State.put
  congr 1
  funext register
  by_cases small : register.val < 4
  · simp [widenRegister, small, Fin.ext_iff]
  · have other : register ≠ widenRegister dst := by
      intro same
      have val := congrArg Fin.val same
      change register.val = dst.val at val
      omega
    simp [small, other]

@[simp] theorem widenState_heap (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).heap = state.heap := rfl

@[simp] theorem widenState_stack (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).stack = state.stack := rfl

@[simp] theorem widenState_output (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).output = state.output := rfl

@[simp] theorem widenState_pc (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).pc = state.pc := rfl

@[simp] theorem widenState_halted (state : State width 4) (saved : Fin 8 → Word width) :
    (widenState state saved).halted = state.halted := rfl

/-- Every original primitive executes in the eight-register machine with the
same heap, stack, output and PC transition; the four high registers are framed. -/
theorem widen_step (instruction : Instruction width 4) (state : State width 4)
    (saved : Fin 8 → Word width) :
    step (widenInstruction instruction) (widenState state saved) =
      (step instruction state).map (fun final => widenState final saved) := by
  cases stopped : state.halted <;> cases instruction <;>
    simp [step, widenInstruction, stopped]
  all_goals first
    | rfl
    | split <;> rfl
    | cases state.stack <;> rfl

def widenProgram (program : Program width 4) : Program width 8 :=
  program.map widenInstruction

/-- Fetched program access uses the same PC and array position after widening. -/
theorem widen_programStep (program : Program width 4) (state : State width 4)
    (saved : Fin 8 → Word width) :
    programStep (widenProgram program) (widenState state saved) =
      (programStep program state).map (fun final => widenState final saved) := by
  unfold programStep
  simp only [widenProgram, widenState, Array.getElem?_map]
  cases found : program[state.pc.val]? with
  | none => rfl
  | some instruction => exact widen_step instruction state saved

/-- Widening carries the complete actual trace without a machine reset. The
additional four registers contribute four charged resident words. -/
theorem widen_execution (program : Program width 4) (state final : State width 4)
    (ticks peak : Nat) (trace : Execution program state final ticks peak)
    (saved : Fin 8 → Word width) :
    Execution (widenProgram program) (widenState state saved)
      (widenState final saved) ticks (peak + 4) := by
  induction trace with
  | refl state =>
    simpa only [widenState_liveWords] using
      Execution.refl (p := widenProgram program) (widenState state saved)
  | @cons start middle final ticks peak transition rest ih =>
    have lifted : programStep (widenProgram program) (widenState start saved) =
        some (widenState middle saved) := by
      rw [widen_programStep, transition]
      rfl
    simpa only [widenState_liveWords, Nat.add_max_add_right] using
      Execution.cons lifted ih

/-- Commit the checked handler's allocated result to its original-ID shared
value slot and reclaim the single transient cell. -/
def commitResultCode (width temporaryAddress nodeBase : Nat) : Program width 8 := #[
  .constant 1 (word width temporaryAddress), .load 0 1,
  .constant 1 (word width nodeBase), .add 1 1 5,
  .store 1 0, .release]

theorem commitResult_execution (program : Program width 8) (state : State width 8)
    (entry temporaryAddress nodeBase identifier : Nat) (value : Word width)
    (present : ∀ phase : Fin 6, program[entry + phase.val]? =
      (commitResultCode width temporaryAddress nodeBase)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 6 < 2 ^ width)
    (temporaryFits : temporaryAddress < 2 ^ width)
    (destinationFits : nodeBase + identifier < 2 ^ width)
    (temporaryBound : temporaryAddress < state.heap.size)
    (destinationBound : nodeBase + identifier < state.heap.size)
    (identifierHeld : state.reg 5 = word width identifier)
    (resultCell : state.heap[temporaryAddress]'temporaryBound = value) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      final.heap = (state.heap.set (nodeBase + identifier) value destinationBound).pop ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 →
        final.reg register = state.reg register) ∧
      final.pc = word width (entry + 6) ∧ final.halted = false := by
  let s1 := state.advance.put 1 (word width temporaryAddress)
  let s2 := s1.advance.put 0 value
  let s3 := s2.advance.put 1 (word width nodeBase)
  let s4 := s3.advance.put 1 (word width (nodeBase + identifier))
  let s5 : State width 8 := { s4.advance with
    heap := state.heap.set (nodeBase + identifier) value destinationBound }
  let final : State width 8 := { s5.advance with heap := s5.heap.pop }
  have temporaryVal : (word width temporaryAddress).val = temporaryAddress := Nat.mod_eq_of_lt temporaryFits
  have baseVal : (word width nodeBase).val = nodeBase := Nat.mod_eq_of_lt (by omega)
  have identifierVal : (word width identifier).val = identifier := Nat.mod_eq_of_lt (by omega)
  have destinationVal : (word width (nodeBase + identifier)).val = nodeBase + identifier := Nat.mod_eq_of_lt destinationFits
  have nonempty : state.heap ≠ #[] := by
    intro empty
    have impossible := temporaryBound
    simp [empty] at impossible
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.put, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.constant 1 (word width temporaryAddress))
      (by simpa using position) (by omega)
      (by simpa [commitResultCode] using present ⟨0, by decide⟩)]
    simp [step, s1, State.put, State.advance, running, temporaryVal,
      baseVal, identifierVal, destinationVal, temporaryBound, destinationBound, identifierHeld, resultCell, nonempty]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.put, State.advance, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.load 0 1)
      (by simpa using p1) (by omega)
      (by simpa [commitResultCode] using present ⟨1, by decide⟩)]
    simp [step, s2, s1, State.put, State.advance, running, temporaryVal,
      baseVal, identifierVal, destinationVal, temporaryBound, destinationBound, identifierHeld, resultCell, nonempty]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.constant 1 (word width nodeBase))
      (by simpa using p2) (by omega)
      (by simpa [commitResultCode] using present ⟨2, by decide⟩)]
    simp [step, s3, s2, s1, State.put, State.advance, running, temporaryVal,
      baseVal, identifierVal, destinationVal, temporaryBound, destinationBound, identifierHeld, resultCell, nonempty]
  have p4 : s4.pc = word width (entry + 4) := by
    simp only [s4, State.put, State.advance, p3]
    rw [show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (by omega)]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.add 1 1 5)
      (by simpa using p3) (by omega)
      (by simpa [commitResultCode] using present ⟨3, by decide⟩)]
    simp [step, s4, s3, s2, s1, State.put, State.advance, running, temporaryVal,
      baseVal, identifierVal, destinationVal, temporaryBound, destinationBound, identifierHeld, resultCell, nonempty]
  have p5 : s5.pc = word width (entry + 5) := by
    simp only [s5, State.put, State.advance, p4]
    rw [show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (by omega)]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.store 1 0)
      (by simpa using p4) (by omega)
      (by simpa [commitResultCode] using present ⟨4, by decide⟩)]
    simp [step, s5, s4, s3, s2, s1, State.put, State.advance, running, temporaryVal,
      baseVal, identifierVal, destinationVal, temporaryBound, destinationBound, identifierHeld, resultCell, nonempty]
  have p6 : final.pc = word width (entry + 6) := by
    simp only [final, State.put, State.advance, p5]
    rw [show (word width (entry + 5)).val = entry + 5 from Nat.mod_eq_of_lt (by omega)]
  have t5 : programStep program s5 = some final := by
    rw [fetched program s5 (entry + 5) (.release)
      (by simpa using p5) (by omega)
      (by simpa [commitResultCode] using present ⟨5, by decide⟩)]
    simp [step, final, s5, s4, s3, s2, s1, State.put, State.advance, running, temporaryVal,
      baseVal, identifierVal, destinationVal, temporaryBound, destinationBound, identifierHeld, resultCell, nonempty]
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, p6, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl final))))))
    have live1 : s1.liveWords = state.liveWords := by
      simp [s1, State.liveWords, State.advance, State.put]
    have live2 : s2.liveWords = state.liveWords := by
      simp [s2, s1, State.liveWords, State.advance, State.put]
    have live3 : s3.liveWords = state.liveWords := by
      simp [s3, s2, s1, State.liveWords, State.advance, State.put]
    have live4 : s4.liveWords = state.liveWords := by
      simp [s4, s3, s2, s1, State.liveWords, State.advance, State.put]
    have live5 : s5.liveWords = state.liveWords := by
      simp [s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put]
    have live6 : final.liveWords ≤ state.liveWords := by
      simp [final, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put] <;> omega
    simpa only [live1, live2, live3, live4, live5, Nat.max_eq_left live6, Nat.max_self] using trace
  · intro register notZero notOne
    simp [final, s5, s4, s3, s2, s1, State.advance, State.put, notZero, notOne]

/-- The allocated result cell is reclaimed after the shared original-ID write. -/
theorem committed_push (heap : Array (Word width)) (destination : Nat)
    (value : Word width) (bound : destination < heap.size) :
    ((heap.push value).set destination value (by simpa using Nat.lt_trans bound (Nat.lt_succ_self _))).pop =
      heap.set destination value bound := by
  rw [Array.set_push, dite_eq_left bound, Array.pop_push]
/-- Fetch each touched original node ID from the actual completion ledger and
clear exactly its node flag and sparse map entry. -/
def resetNodeLedgerCode (width entry done markerBase mapBase : Nat) : Program width 8 := #[
  .branchZero 4 (word width done), .load 0 6,
  .constant 1 (word width markerBase), .add 1 1 0, .store 1 2,
  .constant 1 (word width mapBase), .add 1 1 0, .store 1 2,
  .constant 5 (word width (2 ^ width - 1)), .add 4 4 5,
  .add 6 6 3, .branchZero 2 (word width entry)]

/-- Channel reset traverses the independently stored touched-channel ledger;
node continuation words are never repurposed as channel work entries. -/
def resetChannelLedgerCode (width entry done markerBase : Nat) : Program width 8 := #[
  .branchZero 4 (word width done), .load 0 6,
  .constant 1 (word width markerBase), .add 1 1 0, .store 1 2,
  .constant 5 (word width (2 ^ width - 1)), .add 4 4 5,
  .add 6 6 3, .branchZero 2 (word width entry)]

/-- Clear both live ledger counters after fetched touched-only loops. The dead
ledger contents need not be rewritten and stay within the shared allocation. -/
def resetCountsCode (width nodeCountSlot channelCountSlot : Nat) : Program width 8 := #[
  .constant 1 (word width nodeCountSlot), .store 1 2,
  .constant 1 (word width channelCountSlot), .store 1 2]

structure SharedLayout where
  sourceEnd : Nat
  nodeCount : Nat
  channels : Nat

def SharedLayout.channelValueBase (layout : SharedLayout) := layout.sourceEnd
def SharedLayout.nodeValueBase (layout : SharedLayout) := layout.sourceEnd + layout.channels
def SharedLayout.nodeMarkerBase (layout : SharedLayout) := layout.sourceEnd + layout.channels + layout.nodeCount
def SharedLayout.channelMarkerBase (layout : SharedLayout) := layout.nodeMarkerBase + layout.nodeCount
def SharedLayout.mapBase (layout : SharedLayout) := layout.nodeMarkerBase + layout.nodeCount + layout.channels
def SharedLayout.nodeLedgerBase (layout : SharedLayout) := layout.nodeMarkerBase + 2 * layout.nodeCount + layout.channels
def SharedLayout.channelLedgerBase (layout : SharedLayout) := layout.nodeMarkerBase + 3 * layout.nodeCount + layout.channels
def SharedLayout.nodeCountSlot (layout : SharedLayout) := layout.nodeMarkerBase + 3 * layout.nodeCount + 2 * layout.channels
def SharedLayout.channelCountSlot (layout : SharedLayout) := layout.nodeCountSlot + 1
def SharedLayout.storageEnd (layout : SharedLayout) := layout.nodeCountSlot + 2


/-- A fresh child enters its actual smaller source node while retaining the
parent cursor and remaining count on the charged continuation stack. -/
theorem child_fresh_enter_execution (program : Program width 8) (state : State width 8)
    (entry enter markerBase cursor identifier remaining depth arityBase childDirectory childCount childCursor : Nat)
    (suspendAt : ∀ phase : Fin 2, program[entry + phase.val]? = suspendCode[phase.val]?)
    (touchAt : TouchAt program markerBase (entry + 2))
    (dispatchAt : program[entry + 10]? = some (.branchZero 5 (word width enter)))
    (enterAt : ∀ phase : Fin 10, program[enter + phase.val]? =
      (enterCode width arityBase childDirectory)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 12 < 2 ^ width) (enterFits : enter + 10 < 2 ^ width)
    (cursorFits : cursor < 2 ^ width) (depthFits : depth + 1 < 2 ^ width)
    (cursorHeld : state.reg 6 = word width cursor) (countHeld : state.reg 4 = word width (remaining + 1))
    (depthHeld : state.reg 7 = word width depth)
    (one : state.reg 3 = word width 1)
    (sourceBound : cursor < state.heap.size)
    (source : state.heap[cursor]'sourceBound = word width identifier)
    (markerFits : markerBase + identifier < 2 ^ width)
    (markerBound : markerBase + identifier < state.heap.size)
    (unmarked : state.heap[markerBase + identifier]'markerBound = word width 0)
    (arityFits : arityBase + 2 * identifier < 2 ^ width)
    (directoryFits : childDirectory + 2 * identifier < 2 ^ width)
    (arityBound : arityBase + 2 * identifier < state.heap.size)
    (directoryBound : childDirectory + 2 * identifier < state.heap.size)
    (arityBeforeMarker : arityBase + 2 * identifier < markerBase)
    (directoryBeforeMarker : childDirectory + 2 * identifier < markerBase)
    (arityCell : state.heap[arityBase + 2 * identifier]'arityBound = word width childCount)
    (directoryCell : state.heap[childDirectory + 2 * identifier]'directoryBound = word width childCursor) :
    ∃ final, Execution program state final 20 (state.liveWords + 3) ∧
      final.heap = state.heap.set (markerBase + identifier) (word width 1) markerBound ∧
      final.stack = word width identifier :: word width cursor :: word width (remaining + 1) :: state.stack ∧
      final.output = state.output ∧ final.reg 4 = word width childCount ∧
      final.reg 6 = word width childCursor ∧ final.reg 7 = word width (depth + 1) ∧
      final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧
      final.pc = word width (enter + 10) ∧ final.halted = false := by
  obtain ⟨suspended, first, regs, heap, stack, output, pc, halted⟩ :=
    suspend_execution program state entry suspendAt position running (by omega)
  have suspendedLive : suspended.liveWords = state.liveWords + 2 := by
    simp only [State.liveWords, heap, stack, output, List.length_cons] <;> omega
  obtain ⟨touched, second, touchHeap, touchStack, touchOutput, touchPC, touchRunning,
      cursorPreserved, zeroPreserved, onePreserved, countPreserved, depthPreserved, touchFlag⟩ :=
    touch_fresh program suspended markerBase (entry + 2) cursor identifier touchAt pc halted
      (by omega) (by simpa only [regs] using cursorHeld) cursorFits
      (by simpa only [heap] using sourceBound) (by simpa only [heap] using source)
      markerFits (by simpa only [heap] using markerBound)
      (by simpa only [heap] using unmarked) (by simpa only [regs] using one)
  let dispatched : State width 8 := { touched.advance with pc := word width enter }
  have third : Execution program touched dispatched 1 touched.liveWords :=
    dispatch_fresh program touched (entry + 10) enter dispatchAt
      (by simpa only [Nat.add_assoc] using touchPC) touchRunning (by omega) touchFlag
  have dispatchedStack : dispatched.stack = word width identifier ::
      word width cursor :: word width (remaining + 1) :: state.stack := by
    simp only [dispatched, State.advance, touchStack, stack, regs, cursorHeld, countHeld]
  have dispatchedHeap : dispatched.heap = state.heap.set (markerBase + identifier)
      (word width 1) markerBound := by
    simpa only [dispatched, State.advance, heap] using touchHeap
  have arityAfter : dispatched.heap[arityBase + 2 * identifier]'(by simpa [dispatchedHeap] using arityBound) =
      word width childCount := by
    simp only [dispatchedHeap]
    rw [Array.getElem_set_ne markerBound arityBound (by omega)]
    exact arityCell
  have directoryAfter : dispatched.heap[childDirectory + 2 * identifier]'(by simpa [dispatchedHeap] using directoryBound) =
      word width childCursor := by
    simp only [dispatchedHeap]
    rw [Array.getElem_set_ne markerBound directoryBound (by omega)]
    exact directoryCell
  obtain ⟨final, fourth, finalId, finalDepth, finalCount, finalCursor, finalZero,
      finalOne, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    enter_execution program dispatched enter arityBase childDirectory identifier depth childCount childCursor
      (word width cursor :: word width (remaining + 1) :: state.stack) enterAt rfl
      (by simpa only [dispatched, State.advance] using touchRunning) enterFits dispatchedStack
      (by simpa only [dispatched, State.advance, depthPreserved, regs] using depthHeld)
      (by simpa only [dispatched, State.advance, onePreserved, regs] using one)
      depthFits arityFits directoryFits (by simpa [dispatchedHeap] using arityBound)
      (by simpa [dispatchedHeap] using directoryBound) arityAfter directoryAfter
  have touchedLive : touched.liveWords = state.liveWords + 3 := by
    simp only [State.liveWords, touchHeap, touchStack, touchOutput, heap, stack, output,
      Array.size_set, List.length_cons] <;> omega
  have dispatchedLive : dispatched.liveWords = state.liveWords + 3 := touchedLive
  refine ⟨final, ?_, finalHeap.trans dispatchedHeap, finalStack.trans dispatchedStack,
    ?_, finalCount, finalCursor, finalDepth, ?_, ?_, finalPC, finalRunning⟩
  · have trace := ((first.append second).append third).append fourth
    simpa only [suspendedLive, touchedLive, dispatchedLive, Nat.add_assoc, Nat.max_self, Nat.reduceAdd,
      Nat.max_eq_right (by omega : state.liveWords + 2 ≤ state.liveWords + 3)] using trace
  · simpa only [dispatched, State.advance, touchOutput, output] using finalOutput
  · simpa only [dispatched, State.advance, zeroPreserved, regs] using finalZero
  · simpa only [dispatched, State.advance, onePreserved, regs] using finalOne

def finishReturnCode (width resume rootNext : Nat) : Program width 8 := #[
  .pop 0, .constant 5 (word width (2 ^ width - 1)), .add 7 7 5,
  .branchZero 7 (word width rootNext), .branchZero 2 (word width resume)]

theorem finishReturn_parent (program : Program width 8) (state : State width 8)
    (entry resume rootNext identifier depth : Nat) (suffix : List (Word width))
    (present : ∀ phase : Fin 5, program[entry + phase.val]? =
      (finishReturnCode width resume rootNext)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 5 < 2 ^ width)
    (stack : state.stack = word width identifier :: suffix)
    (depthHeld : state.reg 7 = word width (depth + 1))
    (depthFits : depth + 1 < 2 ^ width) (parent : 0 < depth)
    (zero : state.reg 2 = word width 0) :
    ∃ final, Execution program state final 5 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.reg 7 = word width depth ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 5 → register ≠ 7 →
        final.reg register = state.reg register) ∧
      final.pc = word width resume ∧ final.halted = false := by
  let s1 : State width 8 := { state.advance.put 0 (word width identifier) with stack := suffix }
  let s2 := s1.advance.put 5 (word width (2 ^ width - 1))
  let s3 := s2.advance.put 7 (word width depth)
  let s4 := s3.advance
  let final : State width 8 := { s4.advance with pc := word width resume }
  have depthVal : (word width depth).val = depth := Nat.mod_eq_of_lt (by omega)
  have zeroVal : (word width 0).val = 0 := by simp [word]
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.put, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.put, State.advance, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have p4 : s4.pc = word width (entry + 4) := by
    simp only [s4, State.put, State.advance, p3]
    rw [show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.pop 0)
      (by simpa using position) (by omega)
      (by simpa [finishReturnCode] using present ⟨0, by decide⟩)]
    simp [step, final, s4, s3, s2, s1, State.put, State.advance, running, stack, depthHeld,
      decrement depth depthFits, depthVal, parent.ne', zero, zeroVal]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 5 (word width (2 ^ width - 1)))
      (by simpa using p1) (by omega)
      (by simpa [finishReturnCode] using present ⟨1, by decide⟩)]
    simp [step, final, s4, s3, s2, s1, State.put, State.advance, running, stack, depthHeld,
      decrement depth depthFits, depthVal, parent.ne', zero, zeroVal]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.add 7 7 5)
      (by simpa using p2) (by omega)
      (by simpa [finishReturnCode] using present ⟨2, by decide⟩)]
    simp [step, final, s4, s3, s2, s1, State.put, State.advance, running, stack, depthHeld,
      decrement depth depthFits, depthVal, parent.ne', zero, zeroVal]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.branchZero 7 (word width rootNext))
      (by simpa using p3) (by omega)
      (by simpa [finishReturnCode] using present ⟨3, by decide⟩)]
    simp [step, final, s4, s3, s2, s1, State.put, State.advance, running, stack, depthHeld,
      decrement depth depthFits, depthVal, parent.ne', zero, zeroVal]
  have t4 : programStep program s4 = some final := by
    rw [fetched program s4 (entry + 4) (.branchZero 2 (word width resume))
      (by simpa using p4) (by omega)
      (by simpa [finishReturnCode] using present ⟨4, by decide⟩)]
    simp [step, final, s4, s3, s2, s1, State.put, State.advance, running, stack, depthHeld,
      decrement depth depthFits, depthVal, parent.ne', zero, zeroVal]
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, rfl, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.refl final)))))
    have live1 : s1.liveWords ≤ state.liveWords := by
      simp [final, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live2 : s2.liveWords ≤ state.liveWords := by
      simp [final, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live3 : s3.liveWords ≤ state.liveWords := by
      simp [final, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live4 : s4.liveWords ≤ state.liveWords := by
      simp [final, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live5 : final.liveWords ≤ state.liveWords := by
      simp [final, s4, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have same1 : s1.liveWords = final.liveWords := by simp [final, s4, s3, s2, s1, State.liveWords, State.advance, State.put]
    have same2 : s2.liveWords = final.liveWords := by simp [final, s4, s3, s2, s1, State.liveWords, State.advance, State.put]
    have same3 : s3.liveWords = final.liveWords := by simp [final, s4, s3, s2, s1, State.liveWords, State.advance, State.put]
    have same4 : s4.liveWords = final.liveWords := by simp [final, s4, s3, s2, s1, State.liveWords, State.advance, State.put]
    simpa only [same1, same2, same3, same4, Nat.max_self, Nat.max_eq_left live5] using trace
  · simp [final, s4, s3, State.advance, State.put]
  · intro register notZero notFive notSeven
    simp [final, s4, s3, s2, s1, State.advance, State.put, notZero, notFive, notSeven]

/-- Complete a visited child, publish its source-ID postorder rank, and resume
its parent's original incidence stream on the same machine state. -/
theorem complete_child_resume (program : Program width 8) (state : State width 8)
    (entry returnEntry resume loop rootNext countSlot mapBase ledgerBase identifier rank cursor remaining depth : Nat)
    (suffix : List (Word width))
    (finishAt : ∀ phase : Fin 13, program[entry + phase.val]? =
      (finishLedgerCode width countSlot mapBase ledgerBase)[phase.val]?)
    (returnAt : ∀ phase : Fin 5, program[returnEntry + phase.val]? =
      (finishReturnCode width resume rootNext)[phase.val]?)
    (resumeAt : ∀ phase : Fin 6, program[resume + phase.val]? = (resumeCode width loop)[phase.val]?)
    (joined : returnEntry = entry + 13)
    (position : state.pc = word width entry) (running : state.halted = false)
    (finishFits : entry + 13 < 2 ^ width) (returnFits : returnEntry + 5 < 2 ^ width)
    (resumeFits : resume + 6 < 2 ^ width) (loopFits : loop < 2 ^ width)
    (stack : state.stack = word width identifier :: word width cursor :: word width (remaining + 1) :: suffix)
    (one : state.reg 3 = word width 1) (zero : state.reg 2 = word width 0)
    (depthHeld : state.reg 7 = word width (depth + 1))
    (depthFits : depth + 1 < 2 ^ width) (parent : 0 < depth)
    (cursorFits : cursor + 1 < 2 ^ width) (remainingFits : remaining + 1 < 2 ^ width)
    (countFits : countSlot < 2 ^ width) (mapFits : mapBase + identifier < 2 ^ width)
    (ledgerFits : ledgerBase + rank < 2 ^ width) (rankFits : rank + 1 < 2 ^ width)
    (countBound : countSlot < state.heap.size)
    (mapBound : mapBase + identifier < state.heap.size)
    (ledgerBound : ledgerBase + rank < state.heap.size)
    (countCell : state.heap[countSlot]'countBound = word width rank) :
    ∃ final, Execution program state final 24 state.liveWords ∧
      final.heap = ((state.heap.set (mapBase + identifier) (word width rank) mapBound).set
        (ledgerBase + rank) (word width identifier) (by simpa using ledgerBound)).set
          countSlot (word width (rank + 1)) (by simpa using countBound) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 7 = word width depth ∧ final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧
      final.pc = word width loop ∧ final.halted = false := by
  obtain ⟨completed, first, completedHeap, completedStack, completedOutput,
      completedId, completedRank, completedRegs, completedPC, completedRunning⟩ :=
    finishLedger_execution program state entry countSlot mapBase ledgerBase identifier rank
      (word width cursor :: word width (remaining + 1) :: suffix) finishAt position running
      finishFits stack one countFits mapFits ledgerFits rankFits countBound mapBound ledgerBound countCell
  have completedZero : completed.reg 2 = state.reg 2 := completedRegs 2 (by decide) (by decide) (by decide)
  have completedOne : completed.reg 3 = state.reg 3 := completedRegs 3 (by decide) (by decide) (by decide)
  have completedDepth : completed.reg 7 = state.reg 7 := completedRegs 7 (by decide) (by decide) (by decide)
  obtain ⟨returned, second, returnedHeap, returnedStack, returnedOutput, returnedDepth,
      returnedRegs, returnedPC, returnedRunning⟩ :=
    finishReturn_parent program completed returnEntry resume rootNext identifier depth
      (word width cursor :: word width (remaining + 1) :: suffix) returnAt
      (by simpa only [joined] using completedPC) completedRunning returnFits
      (completedStack.trans stack) (completedDepth.trans depthHeld) depthFits parent
      (completedZero.trans zero)
  have returnedZero : returned.reg 2 = state.reg 2 :=
    (returnedRegs 2 (by decide) (by decide) (by decide)).trans completedZero
  have returnedOne : returned.reg 3 = state.reg 3 :=
    (returnedRegs 3 (by decide) (by decide) (by decide)).trans completedOne
  obtain ⟨final, third, finalCount, finalCursor, finalId, finalZero, finalOne, finalDepth,
      finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    resume_execution program returned resume loop cursor remaining suffix resumeAt returnedPC returnedRunning
      resumeFits loopFits returnedStack (returnedZero.trans zero) (returnedOne.trans one)
      cursorFits remainingFits
  have completedLive : completed.liveWords = state.liveWords := by
    simp only [State.liveWords, completedHeap, Array.size_set, completedStack, completedOutput]
  have returnedLive : returned.liveWords ≤ state.liveWords := by
    simp only [State.liveWords, returnedHeap, completedHeap, Array.size_set,
      returnedStack, returnedOutput, completedOutput, stack, List.length_cons]
    omega
  refine ⟨final, ?_, finalHeap.trans (returnedHeap.trans completedHeap), finalStack,
    finalOutput.trans (returnedOutput.trans completedOutput), finalCount, finalCursor,
    finalDepth.trans returnedDepth, finalZero.trans returnedZero, finalOne.trans returnedOne,
    finalPC, finalRunning⟩
  have trace := (first.append second).append third
  simpa only [completedLive, Nat.max_self, Nat.max_eq_left returnedLive] using trace

def finishChannelCode (width countSlot ledgerBase : Nat) : Program width 8 := #[
  .pop 0, .constant 1 (word width countSlot), .load 5 1,
  .constant 1 (word width ledgerBase), .add 1 1 5, .store 1 0,
  .constant 1 (word width countSlot), .add 5 5 3, .store 1 5]

def scopeTagCode (width tagBase inputEntry : Nat) : Program width 8 := #[
  .constant 1 (word width tagBase), .add 1 1 0, .load 5 1,
  .constant 1 (word width (2 ^ width - 1)), .add 5 5 1,
  .branchZero 5 (word width inputEntry)]

-- Input channel source cursor is the actual head word, one actual occurrence.
def inputScopeCode (width headBase : Nat) : Program width 8 := #[
  .constant 6 (word width headBase), .add 6 6 0, .constant 4 (word width 1)]

-- Actual fixed-code DFS layout; all destinations derived from block lengths.
def setupOffset : Nat := 0
def rootTestOffset : Nat := 5
def rootSuspendOffset : Nat := 6
def rootTouchOffset : Nat := 8
def rootDispatchOffset : Nat := 16
def enterOffset : Nat := 18
def childTestOffset : Nat := 28
def childSuspendOffset : Nat := 29
def childTouchOffset : Nat := 31
def childDispatchOffset : Nat := 39
def childResumeOffset : Nat := 41
def scopeFrameOffset : Nat := 47
def scopeTagOffset : Nat := 50
def guardDirectoryOffset : Nat := 56
def guardJumpOffset : Nat := 62
def inputScopeOffset : Nat := 63
def inputJumpOffset : Nat := 66
def channelTestOffset : Nat := 67
def channelSuspendOffset : Nat := 68
def channelTouchOffset : Nat := 70
def channelDispatchOffset : Nat := 78
def channelPublishOffset : Nat := 80
def channelJumpOffset : Nat := 89
def channelResumeOffset : Nat := 90
def finishLedgerOffset : Nat := 96
def finishReturnOffset : Nat := 109
def rootResumeOffset : Nat := 114
def doneOffset : Nat := 120
def dfsCodeSize : Nat := 120

def dfsProgram (width base childArity childDirectory guardArity guardDirectory tagBase headBase
    nodeMarkers channelMarkers nodeCountSlot channelCountSlot mapBase nodeLedger channelLedger
    rootCursor rootCount : Nat) : Program width 8 :=
  let pcAt := fun offset => base + offset
  #[.constant 7 (word width 0), .constant 2 (word width 0), .constant 3 (word width 1),
    .constant 4 (word width rootCount), .constant 6 (word width rootCursor)] ++
  #[.branchZero 4 (word width (pcAt doneOffset))] ++ suspendCode ++
  touchCode width nodeMarkers (pcAt rootTouchOffset) ++
  #[.branchZero 5 (word width (pcAt enterOffset)), .branchZero 2 (word width (pcAt rootResumeOffset))] ++
  enterCode width childArity childDirectory ++
  #[.branchZero 4 (word width (pcAt scopeFrameOffset))] ++ suspendCode ++
  touchCode width nodeMarkers (pcAt childTouchOffset) ++
  #[.branchZero 5 (word width (pcAt enterOffset)), .branchZero 2 (word width (pcAt childResumeOffset))] ++
  resumeCode width (pcAt childTestOffset) ++ nodeFrameCode ++
  scopeTagCode width tagBase (pcAt inputScopeOffset) ++
  directoryCode width guardArity guardDirectory ++ #[.branchZero 2 (word width (pcAt channelTestOffset))] ++
  inputScopeCode width headBase ++ #[.branchZero 2 (word width (pcAt channelTestOffset))] ++
  #[.branchZero 4 (word width (pcAt finishLedgerOffset))] ++ suspendCode ++
  touchCode width channelMarkers (pcAt channelTouchOffset) ++
  #[.branchZero 5 (word width (pcAt channelPublishOffset)), .branchZero 2 (word width (pcAt channelResumeOffset))] ++
  finishChannelCode width channelCountSlot channelLedger ++
  #[.branchZero 2 (word width (pcAt channelResumeOffset))] ++
  resumeCode width (pcAt channelTestOffset) ++
  finishLedgerCode width nodeCountSlot mapBase nodeLedger ++
  finishReturnCode width (pcAt childResumeOffset) (pcAt rootResumeOffset) ++
  resumeCode width (pcAt rootTestOffset)

/-- Internal source-order discovery specification. This list is produced by
traversal and is never supplied as a precomputed cone to the machine. -/
def discoverNode (graph : DAG n) (root : Fin graph.nodeCount)
    (completed : List (Fin graph.nodeCount)) : List (Fin graph.nodeCount) :=
  if root ∈ completed then completed else
    ((graph.node root).children.foldl (fun completedSoFar child =>
      discoverNode graph (graph.childIndex root child) completedSoFar) completed) ++ [root]
termination_by root.val
decreasing_by exact graph.childIndex_lt root child

def discoverRoots (graph : DAG n) (roots : List (Fin graph.nodeCount)) : List (Fin graph.nodeCount) :=
  roots.foldl (fun completed root => discoverNode graph root completed) []

/-- Original source rows remain in the actual indexed heap across all sparse
marker, ledger and value-table writes. The retained array is the serialized
cache, including ordered child/guard/root occurrences. -/
def CachePrefix (heap source : Array (Word width)) : Prop :=
  ∀ address : Fin source.size, heap[address.val]? = some source[address]

/-- The physical completion ledger and sparse map share the original node
identities; rank is a position in the produced postorder list. -/
structure CompletedStored (layout : SharedLayout) (heap : Array (Word width))
    (graph : DAG n) (completed : List (Fin graph.nodeCount)) : Prop where
  count : heap[layout.nodeCountSlot]? = some (word width completed.length)
  ledger : ∀ position : Fin completed.length,
    heap[layout.nodeLedgerBase + position.val]? = some (word width (completed[position]).val)
  map : ∀ position : Fin completed.length,
    heap[layout.mapBase + (completed[position]).val]? = some (word width position.val)

structure ChannelsStored (layout : SharedLayout) (heap : Array (Word width))
    (channels : List (Channel n)) : Prop where
  count : heap[layout.channelCountSlot]? = some (word width channels.length)
  ledger : ∀ position : Fin channels.length,
    heap[layout.channelLedgerBase + position.val]? = some (word width (channels[position]).val)
  flags : ∀ channel : Channel n,
    heap[layout.channelMarkerBase + channel.val]? =
      some (word width (if channel ∈ channels then 1 else 0))

/-- The traversal's global storage invariant uses original source identity.
The active spine accounts for marks not yet present in the completion ledger. -/
structure TraversalStored (graph : DAG n) (layout : SharedLayout)
    (source : Array (Word width)) (state : State width 8)
    (logical : DFSState graph) (channels : List (Channel n)) : Prop where
  sourceRetained : CachePrefix state.heap source
  nodeDimension : layout.nodeCount = graph.nodeCount
  channelDimension : layout.channels = n
  allocation : state.heap.size = layout.storageEnd
  completed : CompletedStored layout state.heap graph logical.completed
  channelLedger : ChannelsStored layout state.heap channels
  channelsUnique : channels.Nodup
  flags : ∀ node : Fin graph.nodeCount,
    state.heap[layout.nodeMarkerBase + node.val]? = some (word width
      (if node ∈ logical.completed ∨ node ∈ logical.active then 1 else 0))
  completedScope : ∀ node ∈ logical.completed, ∀ channel ∈ (graph.node node).directChannels,
    channel ∈ channels
  depth : state.reg 7 = word width logical.active.length
  zero : state.reg 2 = word width 0
  one : state.reg 3 = word width 1

def freshWeight (graph : DAG n) (completed : List (Fin graph.nodeCount)) : Nat :=
  (completed.map (localNodeWeight graph)).sum

@[simp] theorem freshWeight_append (graph : DAG n)
    (before after : List (Fin graph.nodeCount)) :
    freshWeight graph (before ++ after) = freshWeight graph before + freshWeight graph after := by
  simp [freshWeight]

/-- A source-ID postorder ensures every original child value has been written
before the corresponding parent is evaluated, including repeated child IDs. -/
def Postorder (graph : DAG n) (nodes : List (Fin graph.nodeCount)) : Prop :=
  nodes.Nodup ∧ ∀ position : Fin nodes.length, ∀ child : Fin (nodes[position]).val,
    child ∈ (graph.node (nodes[position])).children →
      graph.childIndex (nodes[position]) child ∈ nodes.take position.val

@[simp] theorem dfsProgram_size (width base childArity childDirectory guardArity guardDirectory tagBase headBase
    nodeMarkers channelMarkers nodeCountSlot channelCountSlot mapBase nodeLedger channelLedger
    rootCursor rootCount : Nat) :
    (dfsProgram width base childArity childDirectory guardArity guardDirectory tagBase headBase
      nodeMarkers channelMarkers nodeCountSlot channelCountSlot mapBase nodeLedger channelLedger
      rootCursor rootCount).size = 120 := by
  simp [dfsProgram, suspendCode, touchCode, enterCode, directoryCode, resumeCode, nodeFrameCode,
    scopeTagCode, inputScopeCode, finishChannelCode, finishLedgerCode, finishReturnCode]

/-- Completion weights telescope across fresh recursive calls. Repeated source
incidences remain in each original node's local weight. -/
theorem freshWeight_suffix (graph : DAG n) (before after middle : List (Fin graph.nodeCount))
    (first : middle = before ++ after) :
    freshWeight graph middle - freshWeight graph before = freshWeight graph after := by
  rw [first, freshWeight_append]
  omega

/-- The concrete DFS code addresses the original retained cache. Pointer and
count constants are derived from its serialized row and root layout. -/
def dfsFromCache (width : Nat) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (base : Nat) (shared : SharedLayout) : Program width 8 :=
  dfsProgram width base
    (caller.size + 4 * rows.length) (caller.size + 2 * rows.length)
    (caller.size + 4 * rows.length + 1) (caller.size + 2 * rows.length + 1)
    caller.size (caller.size + 1)
    shared.nodeMarkerBase shared.channelMarkerBase shared.nodeCountSlot shared.channelCountSlot
    shared.mapBase shared.nodeLedgerBase shared.channelLedgerBase
    (caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
      (ForestIndexedOperands.rowGuards rows).length) roots.length

/-- Every executed scratch store above the retained original cache preserves
all source header and incidence words. -/
theorem cachePrefix_store (heap source : Array (Word width)) (stored : CachePrefix heap source)
    (address : Nat) (value : Word width) (bound : address < heap.size)
    (outside : source.size ≤ address) : CachePrefix (heap.set address value bound) source := by
  intro position
  rw [Array.getElem?_set_ne bound (by have := position.isLt; omega)]
  exact stored position

private theorem completed_capacity (graph : DAG n) (completed : List (Fin graph.nodeCount))
    (unique : completed.Nodup) (node : Fin graph.nodeCount) (fresh : node ∉ completed) :
    completed.length < graph.nodeCount := by
  have distinct : (node :: completed).Nodup := List.nodup_cons.mpr ⟨fresh, unique⟩
  have bounded := distinct.length_le_card
  simp only [List.length_cons, Fintype.card_fin] at bounded
  omega

/-- The actual three completion writes preserve every original cached word. -/
theorem completion_cache_frame (heap source : Array (Word width))
    (layout : SharedLayout) (identifier rank : Nat)
    (stored : CachePrefix heap source) (sourceSize : source.size = layout.sourceEnd)
    (mapBound : layout.mapBase + identifier < heap.size)
    (ledgerBound : layout.nodeLedgerBase + rank < heap.size)
    (countBound : layout.nodeCountSlot < heap.size) :
    CachePrefix (((heap.set (layout.mapBase + identifier) (word width rank) mapBound).set
      (layout.nodeLedgerBase + rank) (word width identifier) (by simpa using ledgerBound)).set
      layout.nodeCountSlot (word width (rank + 1)) (by simpa using countBound)) source := by
  apply cachePrefix_store
  · apply cachePrefix_store
    · apply cachePrefix_store heap source stored
      simp only [sourceSize, SharedLayout.mapBase, SharedLayout.nodeMarkerBase]
      omega
    · simp only [sourceSize, SharedLayout.nodeLedgerBase, SharedLayout.nodeMarkerBase]
      omega
  · simp only [sourceSize, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
    omega

/-- The fetched completion stores append exactly the fresh original node ID to
the physical postorder ledger and publish its original-ID map rank. -/
theorem completion_stored (graph : DAG n) (layout : SharedLayout) (heap : Array (Word width))
    (completed : List (Fin graph.nodeCount)) (node : Fin graph.nodeCount)
    (dimension : layout.nodeCount = graph.nodeCount) (unique : completed.Nodup)
    (fresh : node ∉ completed) (stored : CompletedStored layout heap graph completed)
    (mapBound : layout.mapBase + node.val < heap.size)
    (ledgerBound : layout.nodeLedgerBase + completed.length < heap.size)
    (countBound : layout.nodeCountSlot < heap.size) :
    CompletedStored layout
      (((heap.set (layout.mapBase + node.val) (word width completed.length) mapBound).set
        (layout.nodeLedgerBase + completed.length) (word width node.val) (by simpa using ledgerBound)).set
        layout.nodeCountSlot (word width (completed.length + 1)) (by simpa using countBound))
      graph (completed ++ [node]) := by
  have countRoom : completed.length < layout.nodeCount := by
    rw [dimension]
    exact completed_capacity graph completed unique node fresh
  have nodeRoom : node.val < layout.nodeCount := by rw [dimension]; exact node.isLt
  let heap1 := heap.set (layout.mapBase + node.val) (word width completed.length) mapBound
  let heap2 := heap1.set (layout.nodeLedgerBase + completed.length) (word width node.val)
    (by simpa [heap1] using ledgerBound)
  let final := heap2.set layout.nodeCountSlot (word width (completed.length + 1))
    (by simpa [heap2, heap1] using countBound)
  change CompletedStored layout final graph (completed ++ [node])
  refine ⟨?_, ?_, ?_⟩
  · simp [final, List.length_append]
  · intro position
    have positionRoom : position.val < layout.nodeCount := by
      have bounded := position.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at bounded
      omega
    have countOther : layout.nodeCountSlot ≠ layout.nodeLedgerBase + position.val := by
      simp only [SharedLayout.nodeCountSlot, SharedLayout.nodeLedgerBase]
      omega
    have mapOther : layout.mapBase + node.val ≠ layout.nodeLedgerBase + position.val := by
      simp only [SharedLayout.mapBase, SharedLayout.nodeLedgerBase]
      omega
    by_cases old : position.val < completed.length
    · let previous : Fin completed.length := ⟨position.val, old⟩
      have sameNode : (completed ++ [node])[position] = completed[previous] :=
        List.getElem_append_left old
      have ledgerOther : layout.nodeLedgerBase + completed.length ≠
          layout.nodeLedgerBase + position.val := by omega
      dsimp only [final, heap2, heap1]
      rw [Array.getElem?_set_ne _ countOther, Array.getElem?_set_ne _ ledgerOther,
        Array.getElem?_set_ne _ mapOther, sameNode]
      exact stored.ledger previous
    · have endPosition : position.val = completed.length := by
        have bounded := position.isLt
        simp only [List.length_append, List.length_cons, List.length_nil] at bounded
        omega
      have sameNode : (completed ++ [node])[position] = node := by
        change (completed ++ [node])[position.val]'position.isLt = node
        rw [List.getElem_append_right (as := completed) (bs := [node])
          (i := position.val) (by omega)]
        simp [endPosition]
      dsimp only [final, heap2, heap1]
      rw [Array.getElem?_set_ne _ countOther, sameNode]
      simp only [endPosition, Array.getElem?_set_self]
  · intro position
    by_cases old : position.val < completed.length
    · let previous : Fin completed.length := ⟨position.val, old⟩
      have sameNode : (completed ++ [node])[position] = completed[previous] :=
        List.getElem_append_left old
      have previousRoom : (completed[previous]).val < layout.nodeCount := by
        rw [dimension]
        exact (completed[previous]).isLt
      have countOther : layout.nodeCountSlot ≠ layout.mapBase + (completed[previous]).val := by
        simp only [SharedLayout.nodeCountSlot, SharedLayout.mapBase]
        omega
      have ledgerOther : layout.nodeLedgerBase + completed.length ≠
          layout.mapBase + (completed[previous]).val := by
        simp only [SharedLayout.nodeLedgerBase, SharedLayout.mapBase]
        omega
      have different : node ≠ completed[previous] := by
        intro equal
        apply fresh
        rw [equal]
        exact List.getElem_mem old
      have mapOther : layout.mapBase + node.val ≠ layout.mapBase + (completed[previous]).val := by
        intro equal
        apply different
        apply Fin.ext
        omega
      rw [sameNode]
      dsimp only [final, heap2, heap1]
      rw [Array.getElem?_set_ne _ countOther, Array.getElem?_set_ne _ ledgerOther,
        Array.getElem?_set_ne _ mapOther]
      exact stored.map previous
    · have endPosition : position.val = completed.length := by
        have bounded := position.isLt
        simp only [List.length_append, List.length_cons, List.length_nil] at bounded
        omega
      have sameNode : (completed ++ [node])[position] = node := by
        change (completed ++ [node])[position.val]'position.isLt = node
        rw [List.getElem_append_right (as := completed) (bs := [node])
          (i := position.val) (by omega)]
        simp [endPosition]
      have countOther : layout.nodeCountSlot ≠ layout.mapBase + node.val := by
        simp only [SharedLayout.nodeCountSlot, SharedLayout.mapBase]
        omega
      have ledgerOther : layout.nodeLedgerBase + completed.length ≠ layout.mapBase + node.val := by
        simp only [SharedLayout.nodeLedgerBase, SharedLayout.mapBase]
        omega
      rw [sameNode]
      dsimp only [final, heap2, heap1]
      rw [Array.getElem?_set_ne _ countOther, Array.getElem?_set_ne _ ledgerOther]
      simp only [Array.getElem?_set_self, endPosition]

theorem finishReturn_root (program : Program width 8) (state : State width 8)
    (entry resume rootNext identifier : Nat) (suffix : List (Word width))
    (present : ∀ phase : Fin 5, program[entry + phase.val]? =
      (finishReturnCode width resume rootNext)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 5 < 2 ^ width)
    (stack : state.stack = word width identifier :: suffix)
    (depthHeld : state.reg 7 = word width 1)
    (depthFits : 1 < 2 ^ width)
    (zero : state.reg 2 = word width 0) :
    ∃ final, Execution program state final 4 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.reg 7 = word width 0 ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 5 → register ≠ 7 →
        final.reg register = state.reg register) ∧
      final.pc = word width rootNext ∧ final.halted = false := by
  let s1 : State width 8 := { state.advance.put 0 (word width identifier) with stack := suffix }
  let s2 := s1.advance.put 5 (word width (2 ^ width - 1))
  let s3 := s2.advance.put 7 (word width 0)
  let final : State width 8 := { s3.advance with pc := word width rootNext }
  have zeroVal : (word width 0).val = 0 := by simp [word]
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.put, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.put, State.advance, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.pop 0)
      (by simpa using position) (by omega)
      (by simpa [finishReturnCode] using present ⟨0, by decide⟩)]
    simp [step, final, s3, s2, s1, State.put, State.advance, running, stack, depthHeld,
      decrement 0 depthFits, zero, zeroVal]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 5 (word width (2 ^ width - 1)))
      (by simpa using p1) (by omega)
      (by simpa [finishReturnCode] using present ⟨1, by decide⟩)]
    simp [step, final, s3, s2, s1, State.put, State.advance, running, stack, depthHeld,
      decrement 0 depthFits, zero, zeroVal]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.add 7 7 5)
      (by simpa using p2) (by omega)
      (by simpa [finishReturnCode] using present ⟨2, by decide⟩)]
    simp [step, final, s3, s2, s1, State.put, State.advance, running, stack, depthHeld,
      decrement 0 depthFits, zero, zeroVal]
  have t3 : programStep program s3 = some final := by
    rw [fetched program s3 (entry + 3) (.branchZero 7 (word width rootNext))
      (by simpa using p3) (by omega)
      (by simpa [finishReturnCode] using present ⟨3, by decide⟩)]
    simp [step, final, s3, s2, s1, State.put, State.advance, running, stack, depthHeld,
      decrement 0 depthFits, zero, zeroVal]
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, rfl, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl final))))
    have live1 : s1.liveWords ≤ state.liveWords := by
      simp [final, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live2 : s2.liveWords ≤ state.liveWords := by
      simp [final, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live3 : s3.liveWords ≤ state.liveWords := by
      simp [final, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have live5 : final.liveWords ≤ state.liveWords := by
      simp [final, s3, s2, s1, State.liveWords, State.advance, State.put, stack] <;> omega
    have same1 : s1.liveWords = final.liveWords := by simp [final, s3, s2, s1, State.liveWords, State.advance, State.put]
    have same2 : s2.liveWords = final.liveWords := by simp [final, s3, s2, s1, State.liveWords, State.advance, State.put]
    have same3 : s3.liveWords = final.liveWords := by simp [final, s3, s2, s1, State.liveWords, State.advance, State.put]
    simpa only [same1, same2, same3, Nat.max_self, Nat.max_eq_left live5] using trace
  · simp [final, s3, State.advance, State.put]
  · intro register notZero notFive notSeven
    simp [final, s3, s2, s1, State.advance, State.put, notZero, notFive, notSeven]


theorem finishChannel_execution (program : Program width 8) (state : State width 8)
    (entry countSlot ledgerBase identifier rank : Nat) (suffix : List (Word width))
    (present : ∀ phase : Fin 9, program[entry + phase.val]? =
      (finishChannelCode width countSlot ledgerBase)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 9 < 2 ^ width)
    (stack : state.stack = word width identifier :: suffix)
    (one : state.reg 3 = word width 1)
    (identifierFits : identifier < 2 ^ width)
    (countFits : countSlot < 2 ^ width)
    (ledgerFits : ledgerBase + rank < 2 ^ width)
    (rankFits : rank + 1 < 2 ^ width)
    (countBound : countSlot < state.heap.size)
    (ledgerBound : ledgerBase + rank < state.heap.size)
    (countCell : state.heap[countSlot]'countBound = word width rank) :
    ∃ final, Execution program state final 9 state.liveWords ∧
      final.heap = (state.heap.set (ledgerBase + rank) (word width identifier) ledgerBound).set
        countSlot (word width (rank + 1)) (by simpa using countBound) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 5 →
        final.reg register = state.reg register) ∧
      final.pc = word width (entry + 9) ∧ final.halted = false := by
  let s1 : State width 8 := { state.advance.put 0 (word width identifier) with stack := suffix }
  let s2 : State width 8 := s1.advance.put 1 (word width countSlot)
  let s3 : State width 8 := s2.advance.put 5 (word width rank)
  let s4 : State width 8 := s3.advance.put 1 (word width ledgerBase)
  let s5 : State width 8 := s4.advance.put 1 (word width (ledgerBase + rank))
  let s6 : State width 8 := { s5.advance with heap := state.heap.set (ledgerBase + rank) (word width identifier) ledgerBound }
  let s7 : State width 8 := s6.advance.put 1 (word width countSlot)
  let s8 : State width 8 := s7.advance.put 5 (word width (rank + 1))
  let s9 : State width 8 := { s8.advance with heap := s8.heap.set countSlot (word width (rank + 1)) (by simpa [s8,s7,s6,State.put,State.advance] using countBound) }
  have ledgerBaseFits : ledgerBase < 2 ^ width := by omega
  have rankBaseFits : rank < 2 ^ width := by omega
  have oneFits : 1 < 2 ^ width := by omega
  have idVal : (word width (identifier)).val = identifier := Nat.mod_eq_of_lt identifierFits
  have countVal : (word width (countSlot)).val = countSlot := Nat.mod_eq_of_lt countFits
  have ledgerBaseVal : (word width (ledgerBase)).val = ledgerBase := Nat.mod_eq_of_lt ledgerBaseFits
  have ledgerVal : (word width (ledgerBase + rank)).val = ledgerBase + rank := Nat.mod_eq_of_lt ledgerFits
  have rankVal : (word width (rank)).val = rank := Nat.mod_eq_of_lt rankBaseFits
  have oneVal : (word width (1)).val = 1 := Nat.mod_eq_of_lt oneFits
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.put, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.pop 0)
      (by simpa using position) (by omega)
      (by simpa [finishChannelCode] using present ⟨0, by decide⟩)]
    simp [step, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, ledgerBaseVal, ledgerVal, rankVal, oneVal, countBound, ledgerBound]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.put, State.advance, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 1 (word width countSlot))
      (by simpa using p1) (by omega)
      (by simpa [finishChannelCode] using present ⟨1, by decide⟩)]
    simp [step, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, ledgerBaseVal, ledgerVal, rankVal, oneVal, countBound, ledgerBound]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.load 5 1)
      (by simpa using p2) (by omega)
      (by simpa [finishChannelCode] using present ⟨2, by decide⟩)]
    simp [step, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, ledgerBaseVal, ledgerVal, rankVal, oneVal, countBound, ledgerBound]
  have p4 : s4.pc = word width (entry + 4) := by
    simp only [s4, State.put, State.advance, p3]
    rw [show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (by omega)]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.constant 1 (word width ledgerBase))
      (by simpa using p3) (by omega)
      (by simpa [finishChannelCode] using present ⟨3, by decide⟩)]
    simp [step, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, ledgerBaseVal, ledgerVal, rankVal, oneVal, countBound, ledgerBound]
  have p5 : s5.pc = word width (entry + 5) := by
    simp only [s5, State.put, State.advance, p4]
    rw [show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (by omega)]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 1 1 5)
      (by simpa using p4) (by omega)
      (by simpa [finishChannelCode] using present ⟨4, by decide⟩)]
    simp [step, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, ledgerBaseVal, ledgerVal, rankVal, oneVal, countBound, ledgerBound]
  have p6 : s6.pc = word width (entry + 6) := by
    simp only [s6, State.put, State.advance, p5]
    rw [show (word width (entry + 5)).val = entry + 5 from Nat.mod_eq_of_lt (by omega)]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.store 1 0)
      (by simpa using p5) (by omega)
      (by simpa [finishChannelCode] using present ⟨5, by decide⟩)]
    simp [step, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, ledgerBaseVal, ledgerVal, rankVal, oneVal, countBound, ledgerBound]
  have p7 : s7.pc = word width (entry + 7) := by
    simp only [s7, State.put, State.advance, p6]
    rw [show (word width (entry + 6)).val = entry + 6 from Nat.mod_eq_of_lt (by omega)]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 6) (.constant 1 (word width countSlot))
      (by simpa using p6) (by omega)
      (by simpa [finishChannelCode] using present ⟨6, by decide⟩)]
    simp [step, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, ledgerBaseVal, ledgerVal, rankVal, oneVal, countBound, ledgerBound]
  have p8 : s8.pc = word width (entry + 8) := by
    simp only [s8, State.put, State.advance, p7]
    rw [show (word width (entry + 7)).val = entry + 7 from Nat.mod_eq_of_lt (by omega)]
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (entry + 7) (.add 5 5 3)
      (by simpa using p7) (by omega)
      (by simpa [finishChannelCode] using present ⟨7, by decide⟩)]
    simp [step, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, ledgerBaseVal, ledgerVal, rankVal, oneVal, countBound, ledgerBound]
  have p9 : s9.pc = word width (entry + 9) := by
    simp only [s9, State.put, State.advance, p8]
    rw [show (word width (entry + 8)).val = entry + 8 from Nat.mod_eq_of_lt (by omega)]
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (entry + 8) (.store 1 5)
      (by simpa using p8) (by omega)
      (by simpa [finishChannelCode] using present ⟨8, by decide⟩)]
    simp [step, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, stack, one, countCell,
      countVal, idVal, ledgerBaseVal, ledgerVal, rankVal, oneVal, countBound, ledgerBound]
  refine ⟨s9, ?_, rfl, rfl, rfl, ?_, p9, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl s9)))))))))
    have live1 : s1.liveWords ≤ state.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance, stack] <;> omega
    have live2 : s2.liveWords ≤ state.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance, stack] <;> omega
    have live3 : s3.liveWords ≤ state.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance, stack] <;> omega
    have live4 : s4.liveWords ≤ state.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance, stack] <;> omega
    have live5 : s5.liveWords ≤ state.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance, stack] <;> omega
    have live6 : s6.liveWords ≤ state.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance, stack] <;> omega
    have live7 : s7.liveWords ≤ state.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance, stack] <;> omega
    have live8 : s8.liveWords ≤ state.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance, stack] <;> omega
    have live9 : s9.liveWords ≤ state.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance, stack] <;> omega
    have same1 : s1.liveWords = s9.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance]
    have same2 : s2.liveWords = s9.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance]
    have same3 : s3.liveWords = s9.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance]
    have same4 : s4.liveWords = s9.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance]
    have same5 : s5.liveWords = s9.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance]
    have same6 : s6.liveWords = s9.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance]
    have same7 : s7.liveWords = s9.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance]
    have same8 : s8.liveWords = s9.liveWords := by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.put, State.advance]
    simpa only [same1, same2, same3, same4, same5, same6, same7, same8, Nat.max_self, Nat.max_eq_left live9] using trace
  · intro register notZero notOne notFive
    simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, notZero, notOne, notFive]

/-- The actual stream test either reaches its body or jumps to its terminal block. -/
theorem streamTest_execution (program : Program width 8) (state : State width 8)
    (entry done remaining : Nat)
    (present : program[entry]? = some (.branchZero 4 (word width done)))
    (position : state.pc = word width entry) (running : state.halted = false)
    (entryFits : entry < 2 ^ width) (remainingFits : remaining < 2 ^ width)
    (count : state.reg 4 = word width remaining) :
    Execution program state
      (if remaining = 0 then { state.advance with pc := word width done } else state.advance)
      1 state.liveWords := by
  have countVal : (word width remaining).val = remaining := Nat.mod_eq_of_lt remainingFits
  have transition : programStep program state = some
      (if remaining = 0 then { state.advance with pc := word width done } else state.advance) := by
    rw [fetched program state entry (.branchZero 4 (word width done)) position entryFits present]
    simp [step, running, count, countVal]
  have sameLive : (if remaining = 0 then { state.advance with pc := word width done }
      else state.advance).liveWords = state.liveWords := by split <;> rfl
  simpa only [sameLive, Nat.max_self] using Execution.cons transition (Execution.refl _)

/-- Publish the newly marked channel and restore its node's actual scope cursor. -/
theorem channel_publish_resume (program : Program width 8) (state : State width 8)
    (entry resume loop countSlot ledgerBase identifier rank cursor remaining : Nat)
    (suffix : List (Word width))
    (present : ∀ phase : Fin 9, program[entry + phase.val]? =
      (finishChannelCode width countSlot ledgerBase)[phase.val]?)
    (jumpPresent : program[entry + 9]? = some (.branchZero 2 (word width resume)))
    (resumePresent : ∀ phase : Fin 6, program[resume + phase.val]? =
      (resumeCode width loop)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 10 < 2 ^ width) (resumeFits : resume + 6 < 2 ^ width)
    (loopFits : loop < 2 ^ width)
    (stack : state.stack = word width identifier :: word width cursor ::
      word width (remaining + 1) :: suffix)
    (zero : state.reg 2 = word width 0) (one : state.reg 3 = word width 1)
    (identifierFits : identifier < 2 ^ width) (countFits : countSlot < 2 ^ width)
    (ledgerFits : ledgerBase + rank < 2 ^ width) (rankFits : rank + 1 < 2 ^ width)
    (cursorFits : cursor + 1 < 2 ^ width) (remainingFits : remaining + 1 < 2 ^ width)
    (countBound : countSlot < state.heap.size) (ledgerBound : ledgerBase + rank < state.heap.size)
    (countCell : state.heap[countSlot]'countBound = word width rank) :
    ∃ final, Execution program state final 16 state.liveWords ∧
      final.heap = (state.heap.set (ledgerBase + rank) (word width identifier) ledgerBound).set
        countSlot (word width (rank + 1)) (by simpa using countBound) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 7 = state.reg 7 ∧ final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧
      final.pc = word width loop ∧ final.halted = false := by
  rcases finishChannel_execution program state entry countSlot ledgerBase identifier rank
      (word width cursor :: word width (remaining + 1) :: suffix) present position running
      (by omega) stack one identifierFits countFits ledgerFits rankFits countBound ledgerBound
      countCell with
    ⟨published, publishTrace, publishHeap, publishStack, publishOutput, publishRegisters,
      publishPC, publishRunning⟩
  let jumping : State width 8 := { published.advance with pc := word width resume }
  have publishZero : published.reg 2 = word width 0 := by
    rw [publishRegisters 2 (by decide) (by decide) (by decide)]
    exact zero
  have publishOne : published.reg 3 = word width 1 := by
    rw [publishRegisters 3 (by decide) (by decide) (by decide)]
    exact one
  have transition : programStep program published = some jumping := by
    rw [fetched program published (entry + 9) (.branchZero 2 (word width resume))
      publishPC (by omega) jumpPresent]
    simp [step, jumping, publishRunning, publishZero, word]
  have jumpTrace : Execution program published jumping 1 published.liveWords := by
    simpa only [show jumping.liveWords = published.liveWords from rfl, Nat.max_self]
      using Execution.cons transition (Execution.refl jumping)
  rcases resume_execution program jumping resume loop cursor remaining suffix resumePresent
      rfl publishRunning resumeFits loopFits
      (by simpa [jumping, State.advance] using publishStack)
      (by simpa [jumping, State.advance] using publishZero)
      (by simpa [jumping, State.advance] using publishOne) cursorFits remainingFits with
    ⟨final, resumeTrace, finalCount, finalCursor, finalID, finalZero, finalOne, finalDepth,
      finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩
  have publishedLive : published.liveWords ≤ state.liveWords := by
    simp [State.liveWords, publishHeap, publishStack, publishOutput, stack] <;> omega
  refine ⟨final, ?_, ?_, finalStack, ?_, finalCount, finalCursor, ?_, ?_, ?_, finalPC,
    finalRunning⟩
  · have whole := (publishTrace.append jumpTrace).append resumeTrace
    simpa only [show jumping.liveWords = published.liveWords from rfl, Nat.max_self,
      Nat.max_eq_left publishedLive] using whole
  · exact finalHeap.trans publishHeap
  · exact finalOutput.trans publishOutput
  · exact finalDepth.trans (publishRegisters 7 (by decide) (by decide) (by decide))
  · exact finalZero.trans (publishRegisters 2 (by decide) (by decide) (by decide))
  · exact finalOne.trans (publishRegisters 3 (by decide) (by decide) (by decide))

/-- The ledger charge counts every represented occurrence, with at most a
constant duplicate charge for a guard label and an input channel read. -/
theorem localNodeWeight_bound (graph : DAG n) (node : Fin graph.nodeCount) :
    localNodeWeight graph node ≤
      2 * (1 + (graph.node node).children.length + (graph.node node).guardLabels.length) := by
  cases current : graph.node node <;>
    simp [localNodeWeight, current, Gate.children, Gate.guardLabels, Gate.directChannels] <;>
    omega

/-- Node completion cannot alter the separate physical channel ledger or marks. -/
theorem completion_channels (graph : DAG n) (layout : SharedLayout)
    (heap : Array (Word width)) (completed : List (Fin graph.nodeCount))
    (node : Fin graph.nodeCount) (channels : List (Channel n))
    (nodeDimension : layout.nodeCount = graph.nodeCount)
    (channelDimension : layout.channels = n)
    (nodeUnique : completed.Nodup) (fresh : node ∉ completed)
    (channelUnique : channels.Nodup) (stored : ChannelsStored layout heap channels)
    (mapBound : layout.mapBase + node.val < heap.size)
    (ledgerBound : layout.nodeLedgerBase + completed.length < heap.size)
    (countBound : layout.nodeCountSlot < heap.size) :
    ChannelsStored layout
      (((heap.set (layout.mapBase + node.val) (word width completed.length) mapBound).set
        (layout.nodeLedgerBase + completed.length) (word width node.val) (by simpa using ledgerBound)).set
        layout.nodeCountSlot (word width (completed.length + 1)) (by simpa using countBound))
      channels := by
  have nodeRoom : node.val < layout.nodeCount := by rw [nodeDimension]; exact node.isLt
  have completedRoom : completed.length < layout.nodeCount := by
    rw [nodeDimension]
    exact completed_capacity graph completed nodeUnique node fresh
  have channelRoom : channels.length ≤ layout.channels := by
    rw [channelDimension]
    simpa only [Fintype.card_fin] using channelUnique.length_le_card
  have preserve : ∀ address, (address = layout.channelCountSlot ∨
      (layout.channelLedgerBase ≤ address ∧ address < layout.channelLedgerBase + channels.length) ∨
      (layout.channelMarkerBase ≤ address ∧ address < layout.channelMarkerBase + layout.channels)) →
      (((heap.set (layout.mapBase + node.val) (word width completed.length) mapBound).set
        (layout.nodeLedgerBase + completed.length) (word width node.val) (by simpa using ledgerBound)).set
        layout.nodeCountSlot (word width (completed.length + 1)) (by simpa using countBound))[address]? =
      heap[address]? := by
    intro address location
    have countOther : layout.nodeCountSlot ≠ address := by
      rcases location with same | ledger | marker
      · simp only [same, SharedLayout.channelCountSlot]; omega
      · simp only [SharedLayout.channelLedgerBase, SharedLayout.nodeCountSlot] at ledger ⊢; omega
      · simp only [SharedLayout.channelMarkerBase, SharedLayout.nodeCountSlot] at marker ⊢; omega
    have ledgerOther : layout.nodeLedgerBase + completed.length ≠ address := by
      rcases location with same | ledger | marker
      · simp only [same, SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot,
          SharedLayout.nodeLedgerBase]; omega
      · simp only [SharedLayout.channelLedgerBase, SharedLayout.nodeLedgerBase] at ledger ⊢; omega
      · simp only [SharedLayout.channelMarkerBase, SharedLayout.nodeLedgerBase] at marker ⊢; omega
    have mapOther : layout.mapBase + node.val ≠ address := by
      rcases location with same | ledger | marker
      · simp only [same, SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot,
          SharedLayout.mapBase]; omega
      · simp only [SharedLayout.channelLedgerBase, SharedLayout.mapBase] at ledger ⊢; omega
      · simp only [SharedLayout.channelMarkerBase, SharedLayout.mapBase] at marker ⊢; omega
    rw [Array.getElem?_set_ne _ countOther, Array.getElem?_set_ne _ ledgerOther,
      Array.getElem?_set_ne _ mapOther]
  refine ⟨?_, ?_, ?_⟩
  · rw [preserve _ (Or.inl rfl)]
    exact stored.count
  · intro position
    rw [preserve _ (Or.inr (Or.inl ⟨by omega, by have := position.isLt; omega⟩))]
    exact stored.ledger position
  · intro channel
    rw [preserve _ (Or.inr (Or.inr ⟨by omega, by have := channel.isLt; omega⟩))]
    exact stored.flags channel

/-- The DFS reads the retained original child slot after arbitrary scratch work. -/
theorem retained_child_cell (caller current : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (corresponds : ForestIndexedOperands.RowsMatch graph rows)
    (stored : CachePrefix current (ForestIndexedOperands.cacheHeap width caller rows roots))
    (node : Fin graph.nodeCount) (slot : Nat) (valid : slot < (graph.node node).children.length) :
    let cursor := caller.size + 6 * rows.length +
      (ForestIndexedOperands.rowChildren (rows.take node.val)).length
    current[cursor + slot]? = some (word width ((graph.node node).children[slot]'valid).val) := by
  dsimp only
  have rowValid : node.val < rows.length := by rw [corresponds.length_eq]; exact node.isLt
  have lengths := congrArg List.length (ForestInputStored.row_children_split rows node.val rowValid)
  simp only [List.length_append, (corresponds.node node).2.2.1, List.length_map] at lengths
  have bounded : caller.size + 6 * rows.length +
      (ForestIndexedOperands.rowChildren (rows.take node.val)).length + slot <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have retained := stored ⟨_, bounded⟩
  have original := ForestInputStored.typed_child_cell caller graph rows roots corresponds node slot valid
  exact retained.trans (congrArg some original)

/-- Guard labels retain original order and multiplicity across marker/ledger writes. -/
theorem retained_guard_cell (caller current : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (corresponds : ForestIndexedOperands.RowsMatch graph rows)
    (stored : CachePrefix current (ForestIndexedOperands.cacheHeap width caller rows roots))
    (node : Fin graph.nodeCount) (slot : Nat) (valid : slot < (graph.node node).guardLabels.length) :
    let cursor := caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
      (ForestIndexedOperands.rowGuards (rows.take node.val)).length
    current[cursor + slot]? = some (word width ((graph.node node).guardLabels[slot]'valid).val) := by
  dsimp only
  have rowValid : node.val < rows.length := by rw [corresponds.length_eq]; exact node.isLt
  have lengths := congrArg List.length (ForestInputStored.row_guards_split rows node.val rowValid)
  simp only [List.length_append, (corresponds.node node).2.2.2, List.length_map] at lengths
  have bounded : caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
      (ForestIndexedOperands.rowGuards (rows.take node.val)).length + slot <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have retained := stored ⟨_, bounded⟩
  have original := ForestInputStored.typed_guard_cell caller graph rows roots corresponds node slot valid
  exact retained.trans (congrArg some original)

/-- Recover the active original source ID from its retained charged frame. -/
theorem nodeFrame_execution (program : Program width 8) (state : State width 8)
    (entry identifier : Nat) (suffix : List (Word width))
    (present : ∀ phase : Fin 3, program[entry + phase.val]? = nodeFrameCode[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 3 < 2 ^ width) (identifierFits : identifier < 2 ^ width)
    (stack : state.stack = word width identifier :: suffix) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width (2 * identifier) ∧
      (∀ register : Fin 8, register ≠ 0 → final.reg register = state.reg register) ∧
      final.pc = word width (entry + 3) ∧ final.halted = false := by
  let s1 : State width 8 := { state.advance.put 0 (word width identifier) with stack := suffix }
  let s2 : State width 8 := { s1.advance with stack := word width identifier :: suffix }
  let final := s2.advance.put 0 (word width (2 * identifier))
  have idVal : (word width identifier).val = identifier := Nat.mod_eq_of_lt identifierFits
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.put, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.advance, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : final.pc = word width (entry + 3) := by
    simp only [final, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry (.pop 0) position (by omega)
      (by simpa [nodeFrameCode] using present ⟨0, by decide⟩)]
    simp [step, s1, running, stack]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.push 0) p1 (by omega)
      (by simpa [nodeFrameCode] using present ⟨1, by decide⟩)]
    simp [step, s2, s1, State.put, State.advance, running]
  have t2 : programStep program s2 = some final := by
    rw [fetched program s2 (entry + 2) (.add 0 0 0) p2 (by omega)
      (by simpa [nodeFrameCode] using present ⟨2, by decide⟩)]
    simp [step, final, s2, s1, State.put, State.advance, running, idVal, two_mul]
  refine ⟨final, ?_, rfl, ?_, rfl, ?_, ?_, p3, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl final)))
    have firstLive : s1.liveWords ≤ state.liveWords := by
      simp [s1, State.liveWords, State.put, State.advance, stack] <;> omega
    have secondLive : s2.liveWords = state.liveWords := by
      simp [s2, s1, State.liveWords, State.put, State.advance, stack]
    have finalLive : final.liveWords = state.liveWords := by
      simp [final, s2, s1, State.liveWords, State.put, State.advance, stack]
    simpa only [secondLive, finalLive, Nat.max_self, Nat.max_eq_right firstLive] using trace
  · simpa [final, s2, s1, State.put, State.advance] using stack.symm
  · simp [final, State.put]
  · intro register other
    simp [final, s2, s1, State.put, State.advance, other]

theorem scopeTag_execution (program : Program width 8) (state : State width 8)
    (entry tagBase inputEntry offset tag : Nat)
    (present : ∀ phase : Fin 6, program[entry + phase.val]? =
      (scopeTagCode width tagBase inputEntry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 6 < 2 ^ width)
    (held : state.reg 0 = word width offset)
    (headerFits : tagBase + offset < 2 ^ width) (tagFits : tag < 2 ^ width)
    (headerBound : tagBase + offset < state.heap.size)
    (header : state.heap[tagBase + offset]'headerBound = word width tag) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      (∀ register : Fin 8, register ≠ 1 → register ≠ 5 → final.reg register = state.reg register) ∧
      final.pc = (if tag = 1 then word width inputEntry else word width (entry + 6)) ∧
      final.halted = false := by
  have capacity : 1 < 2 ^ width := by omega
  have baseFits : tagBase < 2 ^ width := by omega
  have offsetFits : offset < 2 ^ width := by omega
  have baseVal : (word width tagBase).val = tagBase := Nat.mod_eq_of_lt baseFits
  have offsetVal : (word width offset).val = offset := Nat.mod_eq_of_lt offsetFits
  have headerVal : (word width (tagBase + offset)).val = tagBase + offset := Nat.mod_eq_of_lt headerFits
  have tagVal : (word width tag).val = tag := Nat.mod_eq_of_lt tagFits
  have minusVal : (word width (2 ^ width - 1)).val = 2 ^ width - 1 := Nat.mod_eq_of_lt (by omega)
  have flagZero : (word width (tag + (2 ^ width - 1))).val = 0 ↔ tag = 1 := by
    by_cases empty : tag = 0
    · simp only [empty, Nat.zero_add, word]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have sum : tag + (2 ^ width - 1) = (tag - 1) + 2 ^ width := by omega
      simp only [word, sum, Nat.add_mod_right]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
  let s1 : State width 8 := state.advance.put 1 (word width tagBase)
  let s2 : State width 8 := s1.advance.put 1 (word width (tagBase + offset))
  let s3 : State width 8 := s2.advance.put 5 (word width tag)
  let s4 : State width 8 := s3.advance.put 1 (word width (2 ^ width - 1))
  let s5 : State width 8 := s4.advance.put 5 (word width (tag + (2 ^ width - 1)))
  let s6 : State width 8 := if tag = 1 then { s5.advance with pc := word width inputEntry } else s5.advance
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.put, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.put, State.advance, p1]
    rw [show (word width (entry + 1)).val = (entry + 1) from Nat.mod_eq_of_lt (by omega)]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = (entry + 2) from Nat.mod_eq_of_lt (by omega)]
  have p4 : s4.pc = word width (entry + 4) := by
    simp only [s4, State.put, State.advance, p3]
    rw [show (word width (entry + 3)).val = (entry + 3) from Nat.mod_eq_of_lt (by omega)]
  have p5 : s5.pc = word width (entry + 5) := by
    simp only [s5, State.put, State.advance, p4]
    rw [show (word width (entry + 4)).val = (entry + 4) from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.constant 1 (word width tagBase))
      (by simpa using position) (by omega)
      (by simpa [scopeTagCode] using present ⟨0, by decide⟩)]
    simp [step, s1, State.put, State.advance, running, held, header,
      baseVal, offsetVal, headerVal, tagVal, minusVal, headerBound, flagZero]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.add 1 1 0)
      (by simpa using p1) (by omega)
      (by simpa [scopeTagCode] using present ⟨1, by decide⟩)]
    simp [step, s2, s1, State.put, State.advance, running, held, header,
      baseVal, offsetVal, headerVal, tagVal, minusVal, headerBound, flagZero]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.load 5 1)
      (by simpa using p2) (by omega)
      (by simpa [scopeTagCode] using present ⟨2, by decide⟩)]
    simp [step, s3, s2, s1, State.put, State.advance, running, held, header,
      baseVal, offsetVal, headerVal, tagVal, minusVal, headerBound, flagZero]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.constant 1 (word width (2 ^ width - 1)))
      (by simpa using p3) (by omega)
      (by simpa [scopeTagCode] using present ⟨3, by decide⟩)]
    simp [step, s4, s3, s2, s1, State.put, State.advance, running, held, header,
      baseVal, offsetVal, headerVal, tagVal, minusVal, headerBound, flagZero]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 5 5 1)
      (by simpa using p4) (by omega)
      (by simpa [scopeTagCode] using present ⟨4, by decide⟩)]
    simp [step, s5, s4, s3, s2, s1, State.put, State.advance, running, held, header,
      baseVal, offsetVal, headerVal, tagVal, minusVal, headerBound, flagZero]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.branchZero 5 (word width inputEntry))
      (by simpa using p5) (by omega)
      (by simpa [scopeTagCode] using present ⟨5, by decide⟩)]
    simp [step, s6, s5, s4, s3, s2, s1, State.put, State.advance, running, held, header,
      baseVal, offsetVal, headerVal, tagVal, minusVal, headerBound, flagZero]
  refine ⟨s6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl s6))))))
    have live1 : s1.liveWords = state.liveWords := by rfl
    have live2 : s2.liveWords = state.liveWords := by rfl
    have live3 : s3.liveWords = state.liveWords := by rfl
    have live4 : s4.liveWords = state.liveWords := by rfl
    have live5 : s5.liveWords = state.liveWords := by rfl
    have live6 : s6.liveWords = state.liveWords := by dsimp only [s6]; split <;> rfl
    simpa only [live1, live2, live3, live4, live5, live6, Nat.max_self] using trace
  · dsimp only [s6]
    split <;> rfl
  · dsimp only [s6]
    split <;> rfl
  · dsimp only [s6]
    split <;> rfl
  · intro register notOne notFive
    dsimp only [s6]
    split <;> simp [s5, s4, s3, s2, s1, State.put, State.advance, notOne, notFive]
  · by_cases input : tag = 1
    · simp only [s6, input, ite_true]
    · simp only [s6, input, ite_false, State.advance, p5]
      rw [show (word width (entry + 5)).val = entry + 5 from Nat.mod_eq_of_lt (by omega)]
  · dsimp only [s6]
    split <;> exact running

/-- Consume one fresh original scope occurrence on the fixed DFS program. -/
theorem channel_fresh_execution (program : Program width 8) (state : State width 8)
    (entry publish resume loop markerBase countSlot ledgerBase cursor identifier remaining rank : Nat)
    (suspendAt : ∀ phase : Fin 2, program[entry + phase.val]? = suspendCode[phase.val]?)
    (touchAt : TouchAt program markerBase (entry + 2))
    (dispatchAt : program[entry + 10]? = some (.branchZero 5 (word width publish)))
    (publishAt : ∀ phase : Fin 9, program[publish + phase.val]? =
      (finishChannelCode width countSlot ledgerBase)[phase.val]?)
    (jumpAt : program[publish + 9]? = some (.branchZero 2 (word width resume)))
    (resumeAt : ∀ phase : Fin 6, program[resume + phase.val]? = (resumeCode width loop)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 12 < 2 ^ width) (publishFits : publish + 10 < 2 ^ width)
    (resumeFits : resume + 6 < 2 ^ width) (loopFits : loop < 2 ^ width)
    (cursorHeld : state.reg 6 = word width cursor) (countHeld : state.reg 4 = word width (remaining + 1))
    (zero : state.reg 2 = word width 0) (one : state.reg 3 = word width 1)
    (cursorFits : cursor + 1 < 2 ^ width) (remainingFits : remaining + 1 < 2 ^ width)
    (sourceBound : cursor < state.heap.size) (source : state.heap[cursor]'sourceBound = word width identifier)
    (markerFits : markerBase + identifier < 2 ^ width)
    (markerBound : markerBase + identifier < state.heap.size)
    (unmarked : state.heap[markerBase + identifier]'markerBound = word width 0)
    (countFits : countSlot < 2 ^ width) (ledgerFits : ledgerBase + rank < 2 ^ width)
    (rankFits : rank + 1 < 2 ^ width)
    (countBound : countSlot < state.heap.size) (ledgerBound : ledgerBase + rank < state.heap.size)
    (markerBeforeCount : markerBase + identifier < countSlot)
    (countCell : state.heap[countSlot]'countBound = word width rank) :
    ∃ final, Execution program state final 26 (state.liveWords + 3) ∧
      final.heap = ((state.heap.set (markerBase + identifier) (word width 1) markerBound).set
        (ledgerBase + rank) (word width identifier) (by simpa using ledgerBound)).set
          countSlot (word width (rank + 1)) (by simpa using countBound) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 7 = state.reg 7 ∧ final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧
      final.pc = word width loop ∧ final.halted = false := by
  obtain ⟨suspended, first, regs, heap, stack, output, pc, halted⟩ :=
    suspend_execution program state entry suspendAt position running (by omega)
  have suspendedLive : suspended.liveWords = state.liveWords + 2 := by
    simp only [State.liveWords, heap, stack, output, List.length_cons] <;> omega
  obtain ⟨touched, second, touchHeap, touchStack, touchOutput, touchPC, touchRunning,
      cursorPreserved, zeroPreserved, onePreserved, countPreserved, depthPreserved, touchFlag⟩ :=
    touch_fresh program suspended markerBase (entry + 2) cursor identifier touchAt pc halted
      (by omega) (by simpa only [regs] using cursorHeld) (by omega)
      (by simpa only [heap] using sourceBound) (by simpa only [heap] using source)
      markerFits (by simpa only [heap] using markerBound)
      (by simpa only [heap] using unmarked) (by simpa only [regs] using one)
  let dispatched : State width 8 := { touched.advance with pc := word width publish }
  have third : Execution program touched dispatched 1 touched.liveWords :=
    dispatch_fresh program touched (entry + 10) publish dispatchAt
      (by simpa only [Nat.add_assoc] using touchPC) touchRunning (by omega) touchFlag
  have dispatchedStack : dispatched.stack = word width identifier ::
      word width cursor :: word width (remaining + 1) :: state.stack := by
    simp only [dispatched, State.advance, touchStack, stack, regs, cursorHeld, countHeld]
  have dispatchedHeap : dispatched.heap = state.heap.set (markerBase + identifier)
      (word width 1) markerBound := by
    simpa only [dispatched, State.advance, heap] using touchHeap
  have countAfter : dispatched.heap[countSlot]'(by simpa [dispatchedHeap] using countBound) =
      word width rank := by
    simp only [dispatchedHeap]
    rw [Array.getElem_set_ne markerBound countBound (by omega)]
    exact countCell
  obtain ⟨final, fourth, finalHeap, finalStack, finalOutput, finalCount, finalCursor,
      finalDepth, finalZero, finalOne, finalPC, finalRunning⟩ :=
    channel_publish_resume program dispatched publish resume loop countSlot ledgerBase identifier rank
      cursor remaining state.stack publishAt jumpAt resumeAt rfl touchRunning publishFits resumeFits
      loopFits dispatchedStack (by simpa [dispatched, State.advance, zeroPreserved, regs] using zero)
      (by simpa [dispatched, State.advance, onePreserved, regs] using one) (by omega)
      countFits ledgerFits rankFits cursorFits remainingFits
      (by simpa [dispatchedHeap] using countBound) (by simpa [dispatchedHeap] using ledgerBound) countAfter
  have touchedLive : touched.liveWords = state.liveWords + 3 := by
    simp only [State.liveWords, touchHeap, Array.size_set, touchStack, touchOutput,
      heap, stack, output, List.length_cons] <;> omega
  have dispatchedLive : dispatched.liveWords = state.liveWords + 3 := by
    change touched.liveWords = state.liveWords + 3
    exact touchedLive
  refine ⟨final, ?_, ?_, finalStack, ?_, finalCount, finalCursor, ?_, ?_, ?_, finalPC,
    finalRunning⟩
  · have whole := ((first.append second).append third).append fourth
    simpa only [suspendedLive, touchedLive, dispatchedLive,
      Nat.max_self, Nat.max_eq_right (by omega : state.liveWords + 2 ≤ state.liveWords + 3)] using whole
  · simpa only [dispatchedHeap] using finalHeap
  · simpa only [dispatched, State.advance, touchOutput, output] using finalOutput
  · simpa only [dispatched, State.advance, depthPreserved, regs] using finalDepth
  · simpa only [dispatched, State.advance, zeroPreserved, regs] using finalZero
  · simpa only [dispatched, State.advance, onePreserved, regs] using finalOne

/-- Mark-before-push followed by physical publication restores the complete
channel invariant; the newly pending mark is never mistaken for a published ledger ID. -/
theorem channel_publish_stored (layout : SharedLayout) (heap : Array (Word width))
    (channels : List (Channel n)) (channel : Channel n)
    (dimension : layout.channels = n) (unique : channels.Nodup) (fresh : channel ∉ channels)
    (stored : ChannelsStored layout heap channels)
    (markerBound : layout.channelMarkerBase + channel.val < heap.size)
    (ledgerBound : layout.channelLedgerBase + channels.length < heap.size)
    (countBound : layout.channelCountSlot < heap.size) :
    ChannelsStored layout
      (((heap.set (layout.channelMarkerBase + channel.val) (word width 1) markerBound).set
        (layout.channelLedgerBase + channels.length) (word width channel.val) (by simpa using ledgerBound)).set
        layout.channelCountSlot (word width (channels.length + 1)) (by simpa using countBound))
      (channels ++ [channel]) := by
  have countRoom : channels.length < layout.channels := by
    have distinct : (channel :: channels).Nodup := List.nodup_cons.mpr ⟨fresh, unique⟩
    have bounded := distinct.length_le_card
    simp only [List.length_cons, Fintype.card_fin] at bounded
    omega
  have channelRoom : channel.val < layout.channels := by rw [dimension]; exact channel.isLt
  let heap1 := heap.set (layout.channelMarkerBase + channel.val) (word width 1) markerBound
  let heap2 := heap1.set (layout.channelLedgerBase + channels.length) (word width channel.val)
    (by simpa [heap1] using ledgerBound)
  let final := heap2.set layout.channelCountSlot (word width (channels.length + 1))
    (by simpa [heap2, heap1] using countBound)
  change ChannelsStored layout final (channels ++ [channel])
  refine ⟨?_, ?_, ?_⟩
  · simp [final, List.length_append]
  · intro position
    have positionRoom : position.val < layout.channels := by
      have bounded := position.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at bounded
      omega
    have countOther : layout.channelCountSlot ≠ layout.channelLedgerBase + position.val := by
      simp only [SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot,
        SharedLayout.channelLedgerBase]
      omega
    have markerOther : layout.channelMarkerBase + channel.val ≠
        layout.channelLedgerBase + position.val := by
      simp only [SharedLayout.channelMarkerBase, SharedLayout.channelLedgerBase]
      omega
    by_cases old : position.val < channels.length
    · let previous : Fin channels.length := ⟨position.val, old⟩
      have sameChannel : (channels ++ [channel])[position] = channels[previous] :=
        List.getElem_append_left old
      have ledgerOther : layout.channelLedgerBase + channels.length ≠
          layout.channelLedgerBase + position.val := by omega
      dsimp only [final, heap2, heap1]
      rw [Array.getElem?_set_ne _ countOther, Array.getElem?_set_ne _ ledgerOther,
        Array.getElem?_set_ne _ markerOther, sameChannel]
      exact stored.ledger previous
    · have endPosition : position.val = channels.length := by
        have bounded := position.isLt
        simp only [List.length_append, List.length_cons, List.length_nil] at bounded
        omega
      have sameChannel : (channels ++ [channel])[position] = channel := by
        change (channels ++ [channel])[position.val]'position.isLt = channel
        rw [List.getElem_append_right (as := channels) (bs := [channel])
          (i := position.val) (by omega)]
        simp [endPosition]
      dsimp only [final, heap2, heap1]
      rw [Array.getElem?_set_ne _ countOther, sameChannel]
      simp only [endPosition, Array.getElem?_set_self]
  · intro candidate
    have candidateRoom : candidate.val < layout.channels := by rw [dimension]; exact candidate.isLt
    have countOther : layout.channelCountSlot ≠ layout.channelMarkerBase + candidate.val := by
      simp only [SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot,
        SharedLayout.channelMarkerBase]
      omega
    have ledgerOther : layout.channelLedgerBase + channels.length ≠
        layout.channelMarkerBase + candidate.val := by
      simp only [SharedLayout.channelLedgerBase, SharedLayout.channelMarkerBase]
      omega
    dsimp only [final, heap2, heap1]
    rw [Array.getElem?_set_ne _ countOther, Array.getElem?_set_ne _ ledgerOther]
    by_cases same : channel = candidate
    · subst candidate
      simp only [Array.getElem?_set_self, List.mem_append, List.mem_singleton, or_true, ite_true]
    · have markerOther : layout.channelMarkerBase + channel.val ≠
          layout.channelMarkerBase + candidate.val := by
        intro equal
        apply same
        apply Fin.ext
        omega
      rw [Array.getElem?_set_ne _ markerOther, stored.flags candidate]
      simp only [List.mem_append, List.mem_singleton, Ne.symm same, or_false]

/-- The fresh-channel endpoint preserves all source/value/node scratch cells.
Only channel flags, channel ledger words, and the channel count are written. -/
theorem channel_store_frame (layout : SharedLayout) (heap : Array (Word width))
    (identifier rank : Nat) (identifierRoom : identifier < layout.channels)
    (rankRoom : rank < layout.channels)
    (markerBound : layout.channelMarkerBase + identifier < heap.size)
    (ledgerBound : layout.channelLedgerBase + rank < heap.size)
    (countBound : layout.channelCountSlot < heap.size)
    (address : Nat)
    (retained : address < layout.channelMarkerBase ∨
      (layout.mapBase ≤ address ∧ address < layout.channelLedgerBase) ∨
      address = layout.nodeCountSlot) :
    (((heap.set (layout.channelMarkerBase + identifier) (word width 1) markerBound).set
      (layout.channelLedgerBase + rank) (word width identifier) (by simpa using ledgerBound)).set
      layout.channelCountSlot (word width (rank + 1)) (by simpa using countBound))[address]? =
    heap[address]? := by
  have countOther : layout.channelCountSlot ≠ address := by
    rcases retained with below | middle | same
    · simp only [SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot,
        SharedLayout.channelMarkerBase] at below ⊢; omega
    · simp only [SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot,
        SharedLayout.channelLedgerBase] at middle ⊢; omega
    · simp only [same, SharedLayout.channelCountSlot]; omega
  have ledgerOther : layout.channelLedgerBase + rank ≠ address := by
    rcases retained with below | middle | same
    · simp only [SharedLayout.channelLedgerBase, SharedLayout.channelMarkerBase] at below ⊢; omega
    · omega
    · simp only [same, SharedLayout.channelLedgerBase, SharedLayout.nodeCountSlot]; omega
  have markerOther : layout.channelMarkerBase + identifier ≠ address := by
    rcases retained with below | middle | same
    · omega
    · simp only [SharedLayout.channelMarkerBase, SharedLayout.mapBase] at middle ⊢; omega
    · simp only [same, SharedLayout.channelMarkerBase, SharedLayout.nodeCountSlot]; omega
  rw [Array.getElem?_set_ne _ countOther, Array.getElem?_set_ne _ ledgerOther,
    Array.getElem?_set_ne _ markerOther]

/-- Scope-channel publication preserves the complete original-ID node map
and completion ledger, including all rows completed in earlier subtrees. -/
theorem channel_completed_frame (graph : DAG n) (layout : SharedLayout)
    (heap : Array (Word width)) (completed : List (Fin graph.nodeCount))
    (identifier rank : Nat) (dimension : layout.nodeCount = graph.nodeCount)
    (unique : completed.Nodup) (stored : CompletedStored layout heap graph completed)
    (identifierRoom : identifier < layout.channels) (rankRoom : rank < layout.channels)
    (markerBound : layout.channelMarkerBase + identifier < heap.size)
    (ledgerBound : layout.channelLedgerBase + rank < heap.size)
    (countBound : layout.channelCountSlot < heap.size) :
    CompletedStored layout
      (((heap.set (layout.channelMarkerBase + identifier) (word width 1) markerBound).set
        (layout.channelLedgerBase + rank) (word width identifier) (by simpa using ledgerBound)).set
        layout.channelCountSlot (word width (rank + 1)) (by simpa using countBound))
      graph completed := by
  have countRoom : completed.length ≤ layout.nodeCount := by
    rw [dimension]
    simpa only [Fintype.card_fin] using unique.length_le_card
  have preserve := channel_store_frame layout heap identifier rank identifierRoom rankRoom
    markerBound ledgerBound countBound
  refine ⟨?_, ?_, ?_⟩
  · rw [preserve _ (Or.inr (Or.inr rfl))]
    exact stored.count
  · intro position
    have before : layout.mapBase ≤ layout.nodeLedgerBase + position.val ∧
        layout.nodeLedgerBase + position.val < layout.channelLedgerBase := by
      have valid := position.isLt
      simp only [SharedLayout.mapBase, SharedLayout.nodeLedgerBase, SharedLayout.channelLedgerBase]
      omega
    rw [preserve _ (Or.inr (Or.inl before))]
    exact stored.ledger position
  · intro position
    have valid : (completed[position]).val < layout.nodeCount := by
      rw [dimension]
      exact (completed[position]).isLt
    have before : layout.mapBase ≤ layout.mapBase + (completed[position]).val ∧
        layout.mapBase + (completed[position]).val < layout.channelLedgerBase := by
      simp only [SharedLayout.mapBase, SharedLayout.channelLedgerBase]
      omega
    rw [preserve _ (Or.inr (Or.inl before))]
    exact stored.map position

/-- A complete fresh scope iteration carries the physical channel invariant
and frames every original source, value, node marker, map and node ledger cell. -/
theorem channel_fresh_stored (program : Program width 8) (state : State width 8)
    (layout : SharedLayout) (channels : List (Channel n)) (channel : Channel n)
    (entry publish resume loop cursor remaining : Nat)
    (suspendAt : ∀ phase : Fin 2, program[entry + phase.val]? = suspendCode[phase.val]?)
    (touchAt : TouchAt program layout.channelMarkerBase (entry + 2))
    (dispatchAt : program[entry + 10]? = some (.branchZero 5 (word width publish)))
    (publishAt : ∀ phase : Fin 9, program[publish + phase.val]? =
      (finishChannelCode width layout.channelCountSlot layout.channelLedgerBase)[phase.val]?)
    (jumpAt : program[publish + 9]? = some (.branchZero 2 (word width resume)))
    (resumeAt : ∀ phase : Fin 6, program[resume + phase.val]? = (resumeCode width loop)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 12 < 2 ^ width) (publishFits : publish + 10 < 2 ^ width)
    (resumeFits : resume + 6 < 2 ^ width) (loopFits : loop < 2 ^ width)
    (cursorHeld : state.reg 6 = word width cursor) (countHeld : state.reg 4 = word width (remaining + 1))
    (zero : state.reg 2 = word width 0) (one : state.reg 3 = word width 1)
    (cursorFits : cursor + 1 < 2 ^ width) (remainingFits : remaining + 1 < 2 ^ width)
    (sourceBound : cursor < state.heap.size)
    (source : state.heap[cursor]'sourceBound = word width channel.val)
    (dimension : layout.channels = n) (allocation : state.heap.size = layout.storageEnd)
    (storageFits : layout.storageEnd < 2 ^ width)
    (unique : channels.Nodup) (fresh : channel ∉ channels)
    (stored : ChannelsStored layout state.heap channels) :
    ∃ final, Execution program state final 26 (state.liveWords + 3) ∧
      ChannelsStored layout final.heap (channels ++ [channel]) ∧
      final.heap.size = state.heap.size ∧
      (∀ address, address < layout.channelMarkerBase ∨
        (layout.mapBase ≤ address ∧ address < layout.channelLedgerBase) ∨
        address = layout.nodeCountSlot → final.heap[address]? = state.heap[address]?) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 7 = state.reg 7 ∧ final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧
      final.pc = word width loop ∧ final.halted = false := by
  have identifierRoom : channel.val < layout.channels := by rw [dimension]; exact channel.isLt
  have rankRoom : channels.length < layout.channels := by
    have distinct : (channel :: channels).Nodup := List.nodup_cons.mpr ⟨fresh, unique⟩
    have bounded := distinct.length_le_card
    simp only [List.length_cons, Fintype.card_fin] at bounded
    omega
  have markerBound : layout.channelMarkerBase + channel.val < state.heap.size := by
    rw [allocation]
    simp only [SharedLayout.channelMarkerBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have ledgerBound : layout.channelLedgerBase + channels.length < state.heap.size := by
    rw [allocation]
    simp only [SharedLayout.channelLedgerBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have countBound : layout.channelCountSlot < state.heap.size := by
    rw [allocation]
    simp only [SharedLayout.channelCountSlot, SharedLayout.storageEnd]
    omega
  have markerBeforeCount : layout.channelMarkerBase + channel.val < layout.channelCountSlot := by
    simp only [SharedLayout.channelMarkerBase, SharedLayout.channelCountSlot, SharedLayout.nodeCountSlot]
    omega
  have markerFits : layout.channelMarkerBase + channel.val < 2 ^ width := by omega
  have ledgerFits : layout.channelLedgerBase + channels.length < 2 ^ width := by omega
  have countFits : layout.channelCountSlot < 2 ^ width := by omega
  have rankFits : channels.length + 1 < 2 ^ width := by
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot] at storageFits
    omega
  have countCell : state.heap[layout.channelCountSlot]'countBound = word width channels.length := by
    simpa only [Array.getElem?_eq_getElem countBound, Option.some.injEq] using stored.count
  have unmarked : state.heap[layout.channelMarkerBase + channel.val]'markerBound = word width 0 := by
    have flags := stored.flags channel
    simpa only [fresh, ite_false, Array.getElem?_eq_getElem markerBound, Option.some.injEq] using flags
  obtain ⟨final, trace, finalHeap, finalStack, finalOutput, finalCount, finalCursor,
      finalDepth, finalZero, finalOne, finalPC, finalRunning⟩ :=
    channel_fresh_execution program state entry publish resume loop layout.channelMarkerBase
      layout.channelCountSlot layout.channelLedgerBase cursor channel.val remaining channels.length
      suspendAt touchAt dispatchAt publishAt jumpAt resumeAt position running codeFits publishFits
      resumeFits loopFits cursorHeld countHeld zero one cursorFits remainingFits sourceBound source
      markerFits markerBound unmarked countFits ledgerFits rankFits countBound ledgerBound
      markerBeforeCount countCell
  refine ⟨final, trace, ?_, ?_, ?_, finalStack, finalOutput, finalCount, finalCursor, finalDepth,
    finalZero, finalOne, finalPC, finalRunning⟩
  · rw [finalHeap]
    exact channel_publish_stored layout state.heap channels channel dimension unique fresh stored
      markerBound ledgerBound countBound
  · simp only [finalHeap, Array.size_set]
  · intro address retained
    rw [finalHeap]
    exact channel_store_frame layout state.heap channel.val channels.length identifierRoom rankRoom
      markerBound ledgerBound countBound address retained

/-- A scope slice retains the original represented occurrence order. -/
def ScopeStored (heap : Array (Word width)) (cursor : Nat) (labels : List (Channel n)) : Prop :=
  ∀ position : Fin labels.length,
    heap[cursor + position.val]? = some (word width (labels[position]).val)

def publishLabels (channels : List (Channel n)) : List (Channel n) → List (Channel n)
  | [] => channels
  | label :: rest => publishLabels (if label ∈ channels then channels else channels ++ [label]) rest

private theorem scope_tail (heap : Array (Word width)) (cursor : Nat)
    (label : Channel n) (rest : List (Channel n))
    (stored : ScopeStored heap cursor (label :: rest)) : ScopeStored heap (cursor + 1) rest := by
  intro position
  have cell := stored ⟨position.val + 1, by simp only [List.length_cons]; omega⟩
  change heap[cursor + (position.val + 1)]? =
    some (word width ((label :: rest)[position.val + 1]'(by simpa only [List.length_cons] using Nat.succ_lt_succ position.isLt)).val) at cell
  have offset : cursor + (position.val + 1) = cursor + 1 + position.val := by omega
  change heap[cursor + 1 + position.val]? =
    some (word width (rest[position.val]'position.isLt).val)
  simpa only [offset, List.getElem_cons_succ] using cell

private theorem published_nodup (channels : List (Channel n)) (label : Channel n)
    (unique : channels.Nodup) :
    (if label ∈ channels then channels else channels ++ [label]).Nodup := by
  split
  · exact unique
  · rename_i fresh
    rw [List.nodup_append_comm]
    simpa using List.nodup_cons.mpr ⟨fresh, unique⟩

/-- Every premise is an actual fetch in the fixed channel-loop section. -/
structure ScopeCodeAt (program : Program width 8) (layout : SharedLayout)
    (loop publish resume done : Nat) : Prop where
  test : program[loop]? = some (.branchZero 4 (word width done))
  suspend : ∀ phase : Fin 2, program[loop + 1 + phase.val]? = suspendCode[phase.val]?
  touch : TouchAt program layout.channelMarkerBase (loop + 3)
  dispatchFresh : program[loop + 11]? = some (.branchZero 5 (word width publish))
  dispatchStale : program[loop + 12]? = some (.branchZero 2 (word width resume))
  publishCode : ∀ phase : Fin 9, program[publish + phase.val]? =
    (finishChannelCode width layout.channelCountSlot layout.channelLedgerBase)[phase.val]?
  jump : program[publish + 9]? = some (.branchZero 2 (word width resume))
  resumeCodeAt : ∀ phase : Fin 6, program[resume + phase.val]? = (resumeCode width loop)[phase.val]?
  bodyFits : loop + 13 < 2 ^ width
  publishFits : publish + 10 < 2 ^ width
  resumeFits : resume + 6 < 2 ^ width

private theorem channel_iteration (program : Program width 8) (state : State width 8)
    (layout : SharedLayout) (channels : List (Channel n)) (label : Channel n)
    (loop publish resume done cursor remaining : Nat)
    (code : ScopeCodeAt program layout loop publish resume done)
    (position : state.pc = word width (loop + 1)) (running : state.halted = false)
    (cursorHeld : state.reg 6 = word width cursor)
    (countHeld : state.reg 4 = word width (remaining + 1))
    (zero : state.reg 2 = word width 0) (one : state.reg 3 = word width 1)
    (cursorFits : cursor + 1 < 2 ^ width) (remainingFits : remaining + 1 < 2 ^ width)
    (sourceBound : cursor < state.heap.size)
    (source : state.heap[cursor]'sourceBound = word width label.val)
    (dimension : layout.channels = n) (allocation : state.heap.size = layout.storageEnd)
    (storageFits : layout.storageEnd < 2 ^ width) (unique : channels.Nodup)
    (stored : ChannelsStored layout state.heap channels) :
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ 26 ∧
      peak ≤ state.liveWords + 3 ∧
      ChannelsStored layout final.heap (if label ∈ channels then channels else channels ++ [label]) ∧
      final.heap.size = state.heap.size ∧
      (∀ address, address < layout.channelMarkerBase ∨
        (layout.mapBase ≤ address ∧ address < layout.channelLedgerBase) ∨
        address = layout.nodeCountSlot → final.heap[address]? = state.heap[address]?) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 7 = state.reg 7 ∧ final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧
      final.pc = word width loop ∧ final.halted = false := by
  by_cases marked : label ∈ channels
  · have labelRoom : label.val < layout.channels := by rw [dimension]; exact label.isLt
    have markerBound : layout.channelMarkerBase + label.val < state.heap.size := by
      rw [allocation]
      simp only [SharedLayout.channelMarkerBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
      omega
    have markerFits : layout.channelMarkerBase + label.val < 2 ^ width := by omega
    have markerCell : state.heap[layout.channelMarkerBase + label.val]'markerBound = word width 1 := by
      simpa only [marked, ite_true, Array.getElem?_eq_getElem markerBound, Option.some.injEq]
        using stored.flags label
    have nonzero : (word width 1).val ≠ 0 := by
      rw [show (word width 1).val = 1 from Nat.mod_eq_of_lt (by have := code.bodyFits; omega)]
      decide
    obtain ⟨final, trace, finalCount, finalCursor, finalZero, finalOne, finalDepth,
        finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
      child_stale_execution program state (loop + 1) publish resume loop layout.channelMarkerBase
        cursor label.val remaining (word width 1) code.suspend
        (by simpa only [Nat.add_assoc] using code.touch)
        (by simpa only [Nat.add_assoc] using code.dispatchFresh)
        (by simpa only [Nat.add_assoc] using code.dispatchStale) code.resumeCodeAt position running
        (by have := code.bodyFits; omega) code.resumeFits (by have := code.bodyFits; omega)
        cursorFits remainingFits cursorHeld countHeld zero one sourceBound source
        markerFits markerBound markerCell nonzero
    refine ⟨final, 16, state.liveWords + 2, trace, by omega, by omega, ?_, ?_, ?_,
      finalStack, finalOutput, finalCount, finalCursor, finalDepth, finalZero, finalOne,
      finalPC, finalRunning⟩
    · simpa only [marked, ite_true, finalHeap] using stored
    · rw [finalHeap]
    · intro address retained
      rw [finalHeap]
  · obtain ⟨final, trace, finalStored, finalSize, frame, finalStack, finalOutput, finalCount,
        finalCursor, finalDepth, finalZero, finalOne, finalPC, finalRunning⟩ :=
      channel_fresh_stored program state layout channels label (loop + 1) publish resume loop cursor
        remaining code.suspend (by simpa only [Nat.add_assoc] using code.touch)
        (by simpa only [Nat.add_assoc] using code.dispatchFresh) code.publishCode code.jump code.resumeCodeAt
        position running (by have := code.bodyFits; omega) code.publishFits code.resumeFits
        (by have := code.bodyFits; omega) cursorHeld countHeld zero one cursorFits remainingFits
        sourceBound source dimension allocation storageFits unique marked stored
    refine ⟨final, 26, state.liveWords + 3, trace, by omega, le_rfl, ?_, finalSize, frame,
      finalStack, finalOutput, finalCount, finalCursor, finalDepth, finalZero, finalOne,
      finalPC, finalRunning⟩
    simpa only [marked, ite_false] using finalStored

/-- Traverse one complete original scope slice. All steps are fetched from
its fixed code section; every occurrence, including a duplicate, advances the
stored cursor once. Newly published labels come from those source cells. -/
theorem scope_loop_execution (program : Program width 8) (layout : SharedLayout)
    (loop publish resume done : Nat)
    (code : ScopeCodeAt program layout loop publish resume done)
    (dimension : layout.channels = n) (storageFits : layout.storageEnd < 2 ^ width)
    (labels : List (Channel n)) :
    ∀ (state : State width 8) (channels : List (Channel n)) (cursor : Nat),
      state.pc = word width loop → state.halted = false →
      state.heap.size = layout.storageEnd → channels.Nodup →
      ChannelsStored layout state.heap channels →
      state.reg 2 = word width 0 → state.reg 3 = word width 1 →
      state.reg 4 = word width labels.length → state.reg 6 = word width cursor →
      cursor + labels.length ≤ layout.channelMarkerBase → ScopeStored state.heap cursor labels →
      ∃ final ticks peak, Execution program state final ticks peak ∧
        ticks ≤ 27 * labels.length + 1 ∧ peak ≤ state.liveWords + 3 ∧
        ChannelsStored layout final.heap (publishLabels channels labels) ∧
        (publishLabels channels labels).Nodup ∧ final.heap.size = state.heap.size ∧
        (∀ address, address < layout.channelMarkerBase ∨
          (layout.mapBase ≤ address ∧ address < layout.channelLedgerBase) ∨
          address = layout.nodeCountSlot → final.heap[address]? = state.heap[address]?) ∧
        final.stack = state.stack ∧ final.output = state.output ∧
        final.reg 4 = word width 0 ∧ final.reg 6 = word width (cursor + labels.length) ∧
        final.reg 7 = state.reg 7 ∧ final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧
        final.pc = word width done ∧ final.halted = false := by
  induction labels with
  | nil =>
    intro state channels cursor position running allocation unique stored zero one countHeld cursorHeld scopeEnd scope
    let final : State width 8 := { state.advance with pc := word width done }
    have trace : Execution program state final 1 state.liveWords := by
      simpa only [List.length_nil, final, ite_true] using
        streamTest_execution program state loop done 0 code.test position running
          (by have := code.bodyFits; omega) (by have := code.bodyFits; omega) countHeld
    refine ⟨final, 1, state.liveWords, trace, by simp, by omega, stored, unique, rfl, ?_,
      rfl, rfl, countHeld, ?_, rfl, rfl, rfl, rfl, running⟩
    · intro address retained
      rfl
    · change state.reg 6 = word width (cursor + 0)
      simpa only [List.length_nil, Nat.add_zero] using cursorHeld
  | cons label rest ih =>
    intro state channels cursor position running allocation unique stored zero one countHeld cursorHeld scopeEnd scope
    have markerBelowStorage : layout.channelMarkerBase < layout.storageEnd := by
      simp only [SharedLayout.channelMarkerBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
      omega
    have countFits : (label :: rest).length < 2 ^ width := by omega
    let tested : State width 8 := state.advance
    have first : Execution program state tested 1 state.liveWords := by
      simpa [List.length_cons, tested] using
        streamTest_execution program state loop done (label :: rest).length code.test position running
          (by have := code.bodyFits; omega) countFits countHeld
    have testedPC : tested.pc = word width (loop + 1) := by
      simp only [tested, State.advance, position]
      rw [show (word width loop).val = loop from Nat.mod_eq_of_lt (by have := code.bodyFits; omega)]
    have sourceBound : cursor < tested.heap.size := by
      change cursor < state.heap.size
      rw [allocation]
      have length : 0 < (label :: rest).length := by simp
      omega
    have source : tested.heap[cursor]'sourceBound = word width label.val := by
      have cell := scope ⟨0, by simp⟩
      change state.heap[cursor]? = some (word width label.val) at cell
      have stateBound : cursor < state.heap.size := sourceBound
      rw [Array.getElem?_eq_getElem stateBound] at cell
      exact Option.some.inj cell
    obtain ⟨middle, stepTicks, stepPeak, stepTrace, stepTime, stepSpace, middleStored,
        middleSize, middleFrame, middleStack, middleOutput, middleCount, middleCursor,
        middleDepth, middleZero, middleOne, middlePC, middleRunning⟩ :=
      channel_iteration program tested layout channels label loop publish resume done cursor rest.length
        code testedPC running cursorHeld (by simpa only [tested, State.advance, List.length_cons] using countHeld)
        zero one (by
          have length : (label :: rest).length = rest.length + 1 := by simp
          omega)
        (by simpa only [List.length_cons] using countFits) sourceBound source dimension allocation
        storageFits unique stored
    let nextChannels := if label ∈ channels then channels else channels ++ [label]
    have nextUnique : nextChannels.Nodup := published_nodup channels label unique
    have middleAllocation : middle.heap.size = layout.storageEnd := middleSize.trans allocation
    have middleScopeEnd : cursor + 1 + rest.length ≤ layout.channelMarkerBase := by
      simp only [List.length_cons] at scopeEnd
      omega
    have middleScope : ScopeStored middle.heap (cursor + 1) rest := by
      intro position
      rw [middleFrame _ (Or.inl (by have := position.isLt; omega))]
      exact scope_tail state.heap cursor label rest scope position
    obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, finalStored, finalUnique,
        finalSize, finalFrame, finalStack, finalOutput, finalCount, finalCursor, finalDepth,
        finalZero, finalOne, finalPC, finalRunning⟩ :=
      ih middle nextChannels (cursor + 1) middlePC middleRunning middleAllocation nextUnique
        middleStored (middleZero.trans zero) (middleOne.trans one) middleCount middleCursor
        middleScopeEnd middleScope
    have middleLive : middle.liveWords = state.liveWords := by
      simp only [State.liveWords, middleSize, middleStack, middleOutput]
      rfl
    have overallPeak : max (max state.liveWords stepPeak) restPeak ≤ state.liveWords + 3 := by
      apply Nat.max_le.mpr
      refine ⟨Nat.max_le.mpr ⟨by omega, stepSpace⟩, ?_⟩
      simpa only [middleLive] using restSpace
    refine ⟨final, (1 + stepTicks) + restTicks, max (max state.liveWords stepPeak) restPeak,
      (first.append stepTrace).append restTrace, ?_, overallPeak, ?_, ?_,
      finalSize.trans middleSize, ?_, finalStack.trans middleStack,
      finalOutput.trans middleOutput, finalCount, ?_, finalDepth.trans middleDepth,
      finalZero.trans middleZero, finalOne.trans middleOne, finalPC, finalRunning⟩
    · simp only [List.length_cons]
      omega
    · simpa only [publishLabels, nextChannels] using finalStored
    · simpa only [publishLabels, nextChannels] using finalUnique
    · intro address retained
      exact (finalFrame address retained).trans (middleFrame address retained)
    · have sameCursor : cursor + 1 + rest.length = cursor + (label :: rest).length := by
        simp only [List.length_cons]
        omega
      simpa only [sameCursor] using finalCursor

/-- Publishing retains the earlier ledger and adds exactly source labels. -/
theorem publishLabels_mem (channels labels : List (Channel n)) (channel : Channel n) :
    channel ∈ publishLabels channels labels ↔ channel ∈ channels ∨ channel ∈ labels := by
  induction labels generalizing channels with
  | nil => simp [publishLabels]
  | cons label rest ih =>
    simp only [publishLabels, ih, List.mem_cons]
    by_cases already : label ∈ channels
    · simp only [already, ite_true]
      constructor
      · intro h
        rcases h with old | later
        · exact Or.inl old
        · exact Or.inr (Or.inr later)
      · intro h
        rcases h with old | here | later
        · exact Or.inl old
        · exact Or.inl (here.symm ▸ already)
        · exact Or.inr later
    · simp only [already, ite_false, List.mem_append, List.mem_singleton]
      aesop

/-- The complete fetched scope loop preserves the original DFS ledger,
active marks, source cache, and depth while publishing its original labels. -/
theorem scope_loop_global (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width))
    (logical : DFSState graph) (state : State width 8) (channels labels : List (Channel n))
    (loop publish resume done cursor : Nat)
    (code : ScopeCodeAt program layout loop publish resume done)
    (storageFits : layout.storageEnd < 2 ^ width)
    (sourceBelow : source.size ≤ layout.channelMarkerBase)
    (stored : TraversalStored graph layout source state logical channels)
    (position : state.pc = word width loop) (running : state.halted = false)
    (countHeld : state.reg 4 = word width labels.length)
    (cursorHeld : state.reg 6 = word width cursor)
    (scopeEnd : cursor + labels.length ≤ layout.channelMarkerBase)
    (scope : ScopeStored state.heap cursor labels) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 27 * labels.length + 1 ∧ peak ≤ state.liveWords + 3 ∧
      TraversalStored graph layout source final logical (publishLabels channels labels) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 4 = word width 0 ∧ final.reg 6 = word width (cursor + labels.length) ∧
      final.pc = word width done ∧ final.halted = false := by
  obtain ⟨final, ticks, peak, trace, time, space, channelLedger, unique, size, frame,
      stack, output, count, cursorFinal, depth, zero, one, pc, live⟩ :=
    scope_loop_execution program layout loop publish resume done code stored.channelDimension
      storageFits labels state channels cursor position running stored.allocation
      stored.channelsUnique stored.channelLedger stored.zero stored.one countHeld cursorHeld scopeEnd scope
  refine ⟨final, ticks, peak, trace, time, space, ?_, stack, output, count, cursorFinal, pc, live⟩
  refine ⟨?_, stored.nodeDimension, stored.channelDimension, size.trans stored.allocation,
    ?_, channelLedger, unique, ?_, ?_, depth.trans stored.depth,
    zero.trans stored.zero, one.trans stored.one⟩
  · intro address
    rw [frame address.val (Or.inl (by have := address.isLt; omega))]
    exact stored.sourceRetained address
  · refine ⟨?_, ?_, ?_⟩
    · rw [frame layout.nodeCountSlot (Or.inr (Or.inr rfl))]
      exact stored.completed.count
    · intro rank
      rw [frame (layout.nodeLedgerBase + rank.val) (Or.inr (Or.inl (by
        have capacity := logical.completedUnique.length_le_card
        simp only [Fintype.card_fin] at capacity
        have := rank.isLt
        simp only [SharedLayout.mapBase, SharedLayout.nodeLedgerBase, SharedLayout.channelLedgerBase]
        rw [stored.nodeDimension]
        omega)))]
      exact stored.completed.ledger rank
    · intro rank
      rw [frame (layout.mapBase + (logical.completed[rank]).val) (Or.inr (Or.inl (by
        have bound := (logical.completed[rank]).isLt
        simp only [SharedLayout.mapBase, SharedLayout.channelLedgerBase]
        rw [stored.nodeDimension]
        omega)))]
      exact stored.completed.map rank
  · intro node
    rw [frame (layout.nodeMarkerBase + node.val) (Or.inl (by
      have := node.isLt
      simp only [SharedLayout.channelMarkerBase]
      rw [stored.nodeDimension]
      omega))]
    exact stored.flags node
  · intro node member channel scopeMember
    exact (publishLabels_mem channels labels channel).mpr
      (Or.inl (stored.completedScope node member channel scopeMember))

/-- The guard stream consumed by the scope loop is the stored original row,
including repeated labels and its precise serialized occurrence offset. -/
theorem guard_scope_stored (caller current : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (corresponds : ForestIndexedOperands.RowsMatch graph rows)
    (stored : CachePrefix current (ForestIndexedOperands.cacheHeap width caller rows roots))
    (node : Fin graph.nodeCount) :
    ScopeStored current
      (caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
        (ForestIndexedOperands.rowGuards (rows.take node.val)).length)
      (graph.node node).guardLabels := by
  intro position
  change current[(caller.size + 6 * rows.length +
    (ForestIndexedOperands.rowChildren rows).length +
    (ForestIndexedOperands.rowGuards (rows.take node.val)).length) + position.val]? =
      some (word width ((graph.node node).guardLabels[position.val]'position.isLt).val)
  exact retained_guard_cell caller current graph rows roots corresponds stored node
    position.val position.isLt

/-- An input's one scope occurrence is its original serialized head cell. -/
theorem input_scope_stored (caller current : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (corresponds : ForestIndexedOperands.RowsMatch graph rows)
    (stored : CachePrefix current (ForestIndexedOperands.cacheHeap width caller rows roots))
    (node : Fin graph.nodeCount) (channel : Channel n)
    (input : graph.node node = .input channel) :
    ScopeStored current (caller.size + 2 * node.val + 1) [channel] := by
  intro position
  change current[(caller.size + 2 * node.val + 1) + position.val]? =
    some (word width ([channel][position.val]'position.isLt).val)
  have only : position.val = 0 := by have := position.isLt; simp only [List.length_singleton] at this; omega
  have rowBound : node.val < rows.length := by rw [corresponds.length_eq]; exact node.isLt
  have head := ForestIndexedOperands.cache_header_word caller rows roots (2 * node.val + 1)
    (by rw [ForestIndexedOperands.rowHeaders_length]; omega)
  rw [ForestIndexedOperands.header_head_value rows node.val rowBound] at head
  have sourceHead := (corresponds.node node).2.1 channel input
  rw [sourceHead] at head
  have addressBound : caller.size + 2 * node.val + 1 <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have cell := stored ⟨caller.size + 2 * node.val + 1, addressBound⟩
  have exactCell := cell.trans (congrArg some head)
  simpa only [only, Nat.add_zero, List.getElem_cons_zero] using exactCell

private theorem dfs_scope_resume_at (width : Nat) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 6) :
    (dfsFromCache width caller rows roots base layout)[90 + phase.val]? =
      (resumeCode width (base + 67))[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

/-- The complete original-cache-derived 120-instruction program supplies
all fetches used by the arbitrary channel-slice execution. -/
theorem fixed_scope_code (program : Program width 8) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout)
    (physical : ∀ phase : Fin 120, program[base + phase.val]? =
      (dfsFromCache width caller rows roots base layout)[phase.val]?)
    (fits : base + 120 < 2 ^ width) :
    ScopeCodeAt program layout (base + 67) (base + 80) (base + 90) (base + 96) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩
  · simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using physical ⟨67, by decide⟩
  · intro phase
    have cell := physical ⟨68 + phase.val, by have := phase.isLt; omega⟩
    fin_cases phase <;> simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using cell
  · intro phase
    have cell := physical ⟨70 + phase.val, by have := phase.isLt; omega⟩
    fin_cases phase <;> simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using cell
  · simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using physical ⟨78, by decide⟩
  · simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using physical ⟨79, by decide⟩
  · intro phase
    have cell := physical ⟨80 + phase.val, by have := phase.isLt; omega⟩
    fin_cases phase <;> simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using cell
  · simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using physical ⟨89, by decide⟩
  · intro phase
    have cell := physical ⟨90 + phase.val, by have := phase.isLt; omega⟩
    rw [dfs_scope_resume_at] at cell
    simpa only [Nat.add_assoc] using cell

/-- A child excluded from both finished and active nodes is fresh; appending
its active ID preserves uniqueness and separates it from the finished map. -/
def activateChild (graph : DAG n) (logical : DFSState graph)
    (child : Fin graph.nodeCount) (fresh : child ∉ logical.completed)
    (inactive : child ∉ logical.active) : DFSState graph where
  completed := logical.completed
  active := child :: logical.active
  completedUnique := logical.completedUnique
  activeUnique := List.nodup_cons.mpr ⟨inactive, logical.activeUnique⟩
  separate := by
    rw [List.disjoint_cons_right]
    exact ⟨fresh, logical.separate⟩
  closed := logical.closed

/-- Logical transfer at the actual return endpoint: the finished original node
leaves the active spine and enters its produced completion ledger. -/
def completeLogical (graph : DAG n) (logical : DFSState graph)
    (node : Fin graph.nodeCount) (ancestors : List (Fin graph.nodeCount))
    (activeShape : logical.active = node :: ancestors)
    (childrenDone : ∀ child ∈ (graph.node node).children,
      graph.childIndex node child ∈ logical.completed) : DFSState graph where
  completed := logical.completed ++ [node]
  active := ancestors
  completedUnique := by
    have fresh : node ∉ logical.completed := by
      exact (List.disjoint_cons_right.mp (activeShape ▸ logical.separate)).1
    rw [List.nodup_append_comm]
    exact List.nodup_cons.mpr ⟨fresh, logical.completedUnique⟩
  activeUnique := (List.nodup_cons.mp (activeShape ▸ logical.activeUnique)).2
  separate := by
    rw [List.disjoint_left]
    intro candidate completed ancestor
    rcases List.mem_append.mp completed with old | last
    · exact (List.disjoint_left.mp logical.separate old)
        (by rw [activeShape]; exact List.mem_cons_of_mem node ancestor)
    · have same : candidate = node := List.mem_singleton.mp last
      subst candidate
      exact (List.nodup_cons.mp (activeShape ▸ logical.activeUnique)).1 ancestor
  closed := by
    intro candidate completed child incidence
    apply List.mem_append.mpr
    left
    rcases List.mem_append.mp completed with old | last
    · exact logical.closed candidate old child incidence
    · have same : candidate = node := List.mem_singleton.mp last
      subst candidate
      exact childrenDone child incidence

/-- Moving completion at return leaves the physical node-mark set unchanged. -/
theorem completeLogical_mark_set (graph : DAG n) (logical : DFSState graph)
    (node : Fin graph.nodeCount) (ancestors : List (Fin graph.nodeCount))
    (activeShape : logical.active = node :: ancestors)
    (childrenDone : ∀ child ∈ (graph.node node).children,
      graph.childIndex node child ∈ logical.completed)
    (candidate : Fin graph.nodeCount) :
    (candidate ∈ (completeLogical graph logical node ancestors activeShape childrenDone).completed ∨
      candidate ∈ (completeLogical graph logical node ancestors activeShape childrenDone).active) ↔
    (candidate ∈ logical.completed ∨ candidate ∈ logical.active) := by
  simp only [completeLogical, activeShape, List.mem_append, List.mem_singleton, List.mem_cons]
  tauto

/-- The actual completion/return/resume trace publishes a source-ID ledger
entry and restores the parent invariant on the same heap and caller stack. -/
theorem complete_child_global (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width))
    (logical : DFSState graph) (state : State width 8) (channels : List (Channel n))
    (node : Fin graph.nodeCount) (ancestors : List (Fin graph.nodeCount))
    (entry resume loop rootNext cursor remaining : Nat) (suffix : List (Word width))
    (finishAt : ∀ phase : Fin 13, program[entry + phase.val]? =
      (finishLedgerCode width layout.nodeCountSlot layout.mapBase layout.nodeLedgerBase)[phase.val]?)
    (returnAt : ∀ phase : Fin 5, program[entry + 13 + phase.val]? =
      (finishReturnCode width resume rootNext)[phase.val]?)
    (resumeAt : ∀ phase : Fin 6, program[resume + phase.val]? = (resumeCode width loop)[phase.val]?)
    (sourceSize : source.size = layout.sourceEnd)
    (stored : TraversalStored graph layout source state logical channels)
    (activeShape : logical.active = node :: ancestors)
    (parent : 0 < ancestors.length)
    (childrenDone : ∀ child ∈ (graph.node node).children,
      graph.childIndex node child ∈ logical.completed)
    (scopeDone : ∀ channel ∈ (graph.node node).directChannels, channel ∈ channels)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 18 < 2 ^ width) (resumeFits : resume + 6 < 2 ^ width)
    (loopFits : loop < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (depthFits : ancestors.length + 1 < 2 ^ width)
    (cursorFits : cursor + 1 < 2 ^ width) (remainingFits : remaining + 1 < 2 ^ width)
    (stack : state.stack = word width node.val :: word width cursor ::
      word width (remaining + 1) :: suffix) :
    ∃ final, Execution program state final 24 state.liveWords ∧
      TraversalStored graph layout source final
        (completeLogical graph logical node ancestors activeShape childrenDone) channels ∧
      (∀ address, address < layout.nodeMarkerBase → final.heap[address]? = state.heap[address]?) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.pc = word width loop ∧ final.halted = false := by
  have fresh : node ∉ logical.completed :=
    (List.disjoint_cons_right.mp (activeShape ▸ logical.separate)).1
  have nodeRoom : node.val < layout.nodeCount := by rw [stored.nodeDimension]; exact node.isLt
  have rankRoom : logical.completed.length < layout.nodeCount := by
    rw [stored.nodeDimension]
    exact completed_capacity graph logical.completed logical.completedUnique node fresh
  have heapFits : state.heap.size < 2 ^ width := by
    rw [stored.allocation]
    exact storageFits
  have nodeCountFits : layout.nodeCount < 2 ^ width := by
    have below : layout.nodeCount < layout.storageEnd := by
      simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
      omega
    omega
  have mapBound : layout.mapBase + node.val < state.heap.size := by
    rw [stored.allocation]
    simp only [SharedLayout.mapBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have ledgerBound : layout.nodeLedgerBase + logical.completed.length < state.heap.size := by
    rw [stored.allocation]
    simp only [SharedLayout.nodeLedgerBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have countBound : layout.nodeCountSlot < state.heap.size := by
    rw [stored.allocation]
    simp only [SharedLayout.storageEnd]
    omega
  have countCell : state.heap[layout.nodeCountSlot]'countBound = word width logical.completed.length := by
    have cell := stored.completed.count
    rw [Array.getElem?_eq_getElem countBound] at cell
    exact Option.some.inj cell
  obtain ⟨final, trace, heap, caller, output, count, cursorFinal, depth, zero, one, pc, live⟩ :=
    complete_child_resume program state entry (entry + 13) resume loop rootNext
      layout.nodeCountSlot layout.mapBase layout.nodeLedgerBase node.val logical.completed.length
      cursor remaining ancestors.length suffix finishAt returnAt resumeAt rfl position running
      (by omega) (by omega) resumeFits loopFits stack stored.one stored.zero
      (by simpa only [activeShape, List.length_cons, List.length_nil, Nat.zero_add] using stored.depth) depthFits parent
      cursorFits remainingFits (by omega) (by omega) (by omega) (by omega)
      countBound mapBound ledgerBound countCell
  refine ⟨final, trace, ?_, ?_, caller, output, count, cursorFinal, pc, live⟩
  refine ⟨?_, stored.nodeDimension, stored.channelDimension, ?_, ?_, ?_,
    stored.channelsUnique, ?_, ?_, depth, zero.trans stored.zero, one.trans stored.one⟩
  · rw [heap]
    exact completion_cache_frame state.heap source layout node.val logical.completed.length
      stored.sourceRetained sourceSize mapBound ledgerBound countBound
  · simp only [heap, Array.size_set, stored.allocation]
  · rw [heap]
    exact completion_stored graph layout state.heap logical.completed node stored.nodeDimension
      logical.completedUnique fresh stored.completed mapBound ledgerBound countBound
  · rw [heap]
    exact completion_channels graph layout state.heap logical.completed node channels
      stored.nodeDimension stored.channelDimension logical.completedUnique fresh
      stored.channelsUnique stored.channelLedger mapBound ledgerBound countBound
  · intro candidate
    have belowMap : layout.nodeMarkerBase + candidate.val < layout.mapBase := by
      have bound : candidate.val < layout.nodeCount := by rw [stored.nodeDimension]; exact candidate.isLt
      simp only [SharedLayout.mapBase]
      omega
    rw [heap, Array.getElem?_set_ne _ (by
      simp only [SharedLayout.nodeCountSlot, SharedLayout.mapBase] at belowMap ⊢
      omega), Array.getElem?_set_ne _ (by
      simp only [SharedLayout.nodeLedgerBase, SharedLayout.mapBase] at belowMap ⊢
      omega), Array.getElem?_set_ne _ (by omega)]
    simpa only [completeLogical_mark_set] using stored.flags candidate
  · intro candidate completed channel scopeMember
    change candidate ∈ logical.completed ++ [node] at completed
    rcases List.mem_append.mp completed with old | last
    · exact stored.completedScope candidate old channel scopeMember
    · have same : candidate = node := List.mem_singleton.mp last
      subst candidate
      exact scopeDone channel scopeMember
  · intro address beforeMarkers
    have beforeMap : layout.nodeMarkerBase ≤ layout.mapBase := by
      simp only [SharedLayout.mapBase]
      omega
    have beforeLedger : layout.nodeMarkerBase ≤ layout.nodeLedgerBase := by
      simp only [SharedLayout.nodeLedgerBase]
      omega
    have beforeCount : layout.nodeMarkerBase ≤ layout.nodeCountSlot := by
      simp only [SharedLayout.nodeCountSlot]
      omega
    rw [heap, Array.getElem?_set_ne _ (by omega),
      Array.getElem?_set_ne _ (by omega), Array.getElem?_set_ne _ (by omega)]

/-- A fetched fresh source child is marked before being entered. The actual
three-word continuation extends the active spine while all finished storage
and the cold assignment/value prefix are retained. -/
theorem child_fresh_global (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width))
    (logical : DFSState graph) (state : State width 8) (channels : List (Channel n))
    (child : Fin graph.nodeCount) (fresh : child ∉ logical.completed)
    (inactive : child ∉ logical.active)
    (entry enter cursor remaining arityBase childDirectory childCount childCursor : Nat)
    (suspendAt : ∀ phase : Fin 2, program[entry + phase.val]? = suspendCode[phase.val]?)
    (touchAt : TouchAt program layout.nodeMarkerBase (entry + 2))
    (dispatchAt : program[entry + 10]? = some (.branchZero 5 (word width enter)))
    (enterAt : ∀ phase : Fin 10, program[enter + phase.val]? =
      (enterCode width arityBase childDirectory)[phase.val]?)
    (sourceSize : source.size = layout.sourceEnd)
    (stored : TraversalStored graph layout source state logical channels)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 12 < 2 ^ width) (enterFits : enter + 10 < 2 ^ width)
    (storageFits : layout.storageEnd < 2 ^ width)
    (depthFits : logical.active.length + 1 < 2 ^ width)
    (cursorHeld : state.reg 6 = word width cursor)
    (countHeld : state.reg 4 = word width (remaining + 1))
    (cursorBound : cursor < state.heap.size)
    (sourceCell : state.heap[cursor]'cursorBound = word width child.val)
    (arityBound : arityBase + 2 * child.val < state.heap.size)
    (directoryBound : childDirectory + 2 * child.val < state.heap.size)
    (arityBeforeMarker : arityBase + 2 * child.val < layout.nodeMarkerBase)
    (directoryBeforeMarker : childDirectory + 2 * child.val < layout.nodeMarkerBase)
    (arityCell : state.heap[arityBase + 2 * child.val]'arityBound = word width childCount)
    (directoryCell : state.heap[childDirectory + 2 * child.val]'directoryBound = word width childCursor) :
    ∃ final, Execution program state final 20 (state.liveWords + 3) ∧
      TraversalStored graph layout source final (activateChild graph logical child fresh inactive) channels ∧
      (∀ address, address < layout.nodeMarkerBase → final.heap[address]? = state.heap[address]?) ∧
      final.stack = word width child.val :: word width cursor ::
        word width (remaining + 1) :: state.stack ∧ final.output = state.output ∧
      final.reg 4 = word width childCount ∧ final.reg 6 = word width childCursor ∧
      final.pc = word width (enter + 10) ∧ final.halted = false := by
  have childRoom : child.val < layout.nodeCount := by rw [stored.nodeDimension]; exact child.isLt
  have heapFits : state.heap.size < 2 ^ width := by rw [stored.allocation]; exact storageFits
  have markerBound : layout.nodeMarkerBase + child.val < state.heap.size := by
    rw [stored.allocation]
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have markerBeforeMap : layout.nodeMarkerBase + child.val < layout.mapBase := by
    simp only [SharedLayout.mapBase]
    omega
  have markerBeforeChannels : layout.nodeMarkerBase + child.val < layout.channelMarkerBase := by
    simp only [SharedLayout.channelMarkerBase]
    omega
  have markerBeforeLedger : layout.nodeMarkerBase + child.val < layout.nodeLedgerBase := by
    simp only [SharedLayout.nodeLedgerBase]
    omega
  have markerBeforeCount : layout.nodeMarkerBase + child.val < layout.nodeCountSlot := by
    simp only [SharedLayout.nodeCountSlot]
    omega
  have unmarked : state.heap[layout.nodeMarkerBase + child.val]'markerBound = word width 0 := by
    have cell := stored.flags child
    simp only [fresh, inactive, or_self, ite_false] at cell
    rw [Array.getElem?_eq_getElem markerBound] at cell
    exact Option.some.inj cell
  obtain ⟨final, trace, heap, stack, output, count, cursorFinal, depth, zero, one, pc, live⟩ :=
    child_fresh_enter_execution program state entry enter layout.nodeMarkerBase cursor child.val
      remaining logical.active.length arityBase childDirectory childCount childCursor
      suspendAt touchAt dispatchAt enterAt position running codeFits enterFits
      (by omega) depthFits cursorHeld countHeld stored.depth stored.one cursorBound sourceCell
      (by omega) markerBound unmarked (by omega) (by omega) arityBound directoryBound
      arityBeforeMarker directoryBeforeMarker arityCell directoryCell
  refine ⟨final, trace, ?_, ?_, stack, output, count, cursorFinal, pc, live⟩
  · refine ⟨?_, stored.nodeDimension, stored.channelDimension, ?_, ?_, ?_,
      stored.channelsUnique, ?_, stored.completedScope, depth,
      zero.trans stored.zero, one.trans stored.one⟩
    · rw [heap]
      apply cachePrefix_store state.heap source stored.sourceRetained
      simp only [sourceSize, SharedLayout.nodeMarkerBase]
      omega
    · simp only [heap, Array.size_set, stored.allocation]
    · refine ⟨?_, ?_, ?_⟩
      · rw [heap, Array.getElem?_set_ne markerBound (by omega)]
        exact stored.completed.count
      · intro rank
        rw [heap, Array.getElem?_set_ne markerBound (by omega)]
        exact stored.completed.ledger rank
      · intro rank
        rw [heap, Array.getElem?_set_ne markerBound (by omega)]
        exact stored.completed.map rank
    · refine ⟨?_, ?_, ?_⟩
      · have higher : layout.nodeCountSlot < layout.channelCountSlot := by
          simp only [SharedLayout.channelCountSlot]
          omega
        rw [heap, Array.getElem?_set_ne markerBound (by omega)]
        exact stored.channelLedger.count
      · intro rank
        have higher : layout.nodeLedgerBase ≤ layout.channelLedgerBase := by
          simp only [SharedLayout.nodeLedgerBase, SharedLayout.channelLedgerBase]
          omega
        rw [heap, Array.getElem?_set_ne markerBound (by omega)]
        exact stored.channelLedger.ledger rank
      · intro channel
        rw [heap, Array.getElem?_set_ne markerBound (by omega)]
        exact stored.channelLedger.flags channel
    · intro candidate
      by_cases same : candidate = child
      · subst candidate
        rw [heap, Array.getElem?_set_self]
        simp [activateChild]
      · have distinct : layout.nodeMarkerBase + child.val ≠ layout.nodeMarkerBase + candidate.val := by
          intro equal
          apply same
          apply Fin.ext
          omega
        rw [heap, Array.getElem?_set_ne markerBound distinct]
        simpa only [activateChild, List.mem_cons, same, false_or] using stored.flags candidate
  · intro address beforeMarkers
    rw [heap, Array.getElem?_set_ne markerBound (by omega)]


private theorem fresh_space_telescope (before middle after parentLive bodyPeak tailPeak : Nat)
    (bodyPrefix : before ≤ middle) (tailPrefix : middle + 1 ≤ after)
    (bodySpace : bodyPeak ≤ parentLive + 3 + 3 * (middle - before) + 3)
    (tailSpace : tailPeak ≤ parentLive + 3 * (after - (middle + 1)) + 3) :
    max (max (parentLive + 3) bodyPeak) tailPeak ≤ parentLive + 3 * (after - before) + 3 := by
  omega



/-- Internal result of the actual node body. Completion and return are supplied
by the caller's fixed code after this trace ends at offset 96. -/
private structure NodeBodyTrace (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width)) (base : Nat)
    (current : Fin graph.nodeCount) (initial : State width 8)
    (before : DFSState graph) (initialChannels : List (Channel n)) where
  final : State width 8
  logical : DFSState graph
  channels : List (Channel n)
  ticks : Nat
  peak : Nat
  execution : Execution program initial final ticks peak
  charged : ticks + 46 * freshWeight graph before.completed ≤
    46 * freshWeight graph logical.completed + 17 * (graph.node current).children.length +
      27 * (graph.node current).directChannels.length + 18
  space : peak ≤ initial.liveWords + 3 * current.val + 3
  deltaSpace : peak ≤ initial.liveWords +
    3 * (logical.completed.length - before.completed.length) + 3
  stored : TraversalStored graph layout source final logical channels
  active : logical.active = before.active
  completed : logical.completed = (graph.node current).children.foldl
    (fun done child => discoverNode graph (graph.childIndex current child) done) before.completed
  addedPrefix : ∃ added, logical.completed = before.completed ++ added
  childDone : ∀ child ∈ (graph.node current).children,
    graph.childIndex current child ∈ logical.completed
  ownScope : ∀ channel ∈ (graph.node current).directChannels, channel ∈ channels
  inside : ∀ node ∈ logical.completed, node ∈ before.completed ∨ node ∈ graph.cone current
  channelsExact : ∀ channel, channel ∈ channels ↔
    channel ∈ initialChannels ∨ channel ∈ graph.scope current
  postorder : Postorder graph before.completed → Postorder graph logical.completed
  values : ∀ address, address < layout.nodeMarkerBase → final.heap[address]? = initial.heap[address]?
  stack : final.stack = initial.stack
  output : final.output = initial.output
  count : final.reg 4 = word width 0
  depth : final.reg 7 = initial.reg 7
  zero : final.reg 2 = initial.reg 2
  one : final.reg 3 = initial.reg 3
  position : final.pc = word width (base + 96)
  running : final.halted = false

/-- The inner induction consumes original represented child occurrences,
restoring the same node's continuation after every actual fresh or stale path. -/
private structure ChildSliceTrace (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width)) (base : Nat)
    (current : Fin graph.nodeCount) (remaining : List (Fin current.val))
    (cursor : Nat) (initial : State width 8) (before : DFSState graph)
    (initialChannels : List (Channel n)) where
  final : State width 8
  logical : DFSState graph
  channels : List (Channel n)
  ticks : Nat
  peak : Nat
  execution : Execution program initial final ticks peak
  charged : ticks + 46 * freshWeight graph before.completed ≤
    46 * freshWeight graph logical.completed + 17 * remaining.length + 1
  space : peak ≤ initial.liveWords + 3 * current.val + 3
  deltaSpace : peak ≤ initial.liveWords +
    3 * (logical.completed.length - before.completed.length) + 3
  stored : TraversalStored graph layout source final logical channels
  active : logical.active = before.active
  completed : logical.completed = remaining.foldl
    (fun done child => discoverNode graph (graph.childIndex current child) done) before.completed
  addedPrefix : ∃ added, logical.completed = before.completed ++ added
  childDone : ∀ child ∈ remaining, graph.childIndex current child ∈ logical.completed
  inside : ∀ node ∈ logical.completed, node ∈ before.completed ∨ node ∈ graph.cone current
  channelsExact : ∀ channel, channel ∈ channels ↔ channel ∈ initialChannels ∨
    ∃ child ∈ remaining, channel ∈ graph.scope (graph.childIndex current child)
  postorder : Postorder graph before.completed → Postorder graph logical.completed
  values : ∀ address, address < layout.nodeMarkerBase → final.heap[address]? = initial.heap[address]?
  stack : final.stack = initial.stack
  output : final.output = initial.output
  count : final.reg 4 = word width 0
  cursorFinal : final.reg 6 = word width (cursor + remaining.length)
  depth : final.reg 7 = initial.reg 7
  zero : final.reg 2 = initial.reg 2
  one : final.reg 3 = initial.reg 3
  position : final.pc = word width (base + 47)
  running : final.halted = false


/-- Internal fetch interface for the fixed child section; the public containing
program theorem derives it from the original-cache-derived 120-word code. -/
private structure ChildCodeAt (program : Program width 8) (layout : SharedLayout)
    (base arityBase childDirectory : Nat) : Prop where
  test : program[base + 28]? = some (.branchZero 4 (word width (base + 47)))
  suspend : ∀ phase : Fin 2, program[base + 29 + phase.val]? = suspendCode[phase.val]?
  touch : TouchAt program layout.nodeMarkerBase (base + 31)
  dispatchFresh : program[base + 39]? = some (.branchZero 5 (word width (base + 18)))
  dispatchStale : program[base + 40]? = some (.branchZero 2 (word width (base + 41)))
  enterCodeAt : ∀ phase : Fin 10, program[base + 18 + phase.val]? =
    (enterCode width arityBase childDirectory)[phase.val]?
  resumeCodeAt : ∀ phase : Fin 6, program[base + 41 + phase.val]? =
    (resumeCode width (base + 28))[phase.val]?
  finishCodeAt : ∀ phase : Fin 13, program[base + 96 + phase.val]? =
    (finishLedgerCode width layout.nodeCountSlot layout.mapBase layout.nodeLedgerBase)[phase.val]?
  returnCodeAt : ∀ phase : Fin 5, program[base + 109 + phase.val]? =
    (finishReturnCode width (base + 41) (base + 114))[phase.val]?
  fits : base + 120 < 2 ^ width

/-- Every child entry's metadata is an actual original cache cell. Counts and
cursor end bounds account for the whole stored occurrence slice. -/
private structure ChildMetadata (graph : DAG n) (layout : SharedLayout)
    (heap : Array (Word width)) (arityBase childDirectory : Nat)
    (child : Fin graph.nodeCount) where
  cursor : Nat
  arityBound : arityBase + 2 * child.val < heap.size
  directoryBound : childDirectory + 2 * child.val < heap.size
  arityBeforeMarker : arityBase + 2 * child.val < layout.nodeMarkerBase
  directoryBeforeMarker : childDirectory + 2 * child.val < layout.nodeMarkerBase
  arity : heap[arityBase + 2 * child.val]'arityBound = word width (graph.node child).children.length
  directory : heap[childDirectory + 2 * child.val]'directoryBound = word width cursor
  slice : ScopeStored heap cursor (graph.node child).children
  endBound : cursor + (graph.node child).children.length ≤ layout.nodeMarkerBase

private def retained_child_metadata (caller heap : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (layout : SharedLayout)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (retained : CachePrefix heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (allocation : heap.size = layout.storageEnd) (child : Fin graph.nodeCount) :
    ChildMetadata graph layout heap (caller.size + 4 * rows.length)
      (caller.size + 2 * rows.length) child := by
  have valid : child.val < rows.length := by rw [matched.length_eq]; exact child.isLt
  have sourceLength := sourceSize
  simp only [ForestIndexedOperands.cacheHeap_size] at sourceLength
  have sourceBelowHeap : layout.sourceEnd < heap.size := by
    rw [allocation]
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
    omega
  have sourceBelowMarker : layout.sourceEnd ≤ layout.nodeMarkerBase := by
    simp only [SharedLayout.nodeMarkerBase]
    omega
  have aritySource : caller.size + 4 * rows.length + 2 * child.val <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have directorySource : caller.size + 2 * rows.length + 2 * child.val <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have arityBound : caller.size + 4 * rows.length + 2 * child.val < heap.size := by
    rw [sourceSize] at aritySource
    omega
  have directoryBound : caller.size + 2 * rows.length + 2 * child.val < heap.size := by
    rw [sourceSize] at directorySource
    omega
  refine ⟨caller.size + 6 * rows.length +
      (ForestIndexedOperands.rowChildren (rows.take child.val)).length,
    arityBound, directoryBound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sourceSize] at aritySource
    omega
  · rw [sourceSize] at directorySource
    omega
  · have cell := retained ⟨_, aritySource⟩
    have original := ForestIndexedOperands.cache_child_arity_word caller graph rows roots matched child
    have exactCell := cell.trans (congrArg some original)
    rw [Array.getElem?_eq_getElem arityBound] at exactCell
    exact Option.some.inj exactCell
  · have cell := retained ⟨_, directorySource⟩
    have original := (ForestIndexedOperands.cache_base_words caller rows roots child.val valid).1
    have exactCell := cell.trans (congrArg some original)
    rw [Array.getElem?_eq_getElem directoryBound] at exactCell
    exact Option.some.inj exactCell
  · intro position
    change heap[(caller.size + 6 * rows.length +
        (ForestIndexedOperands.rowChildren (rows.take child.val)).length) + position.val]? =
      some (word width ((graph.node child).children[position.val]'position.isLt).val)
    exact retained_child_cell caller heap graph rows roots matched retained child
      position.val position.isLt
  · have lengths := congrArg List.length (ForestInputStored.row_children_split rows child.val valid)
    simp only [List.length_append, (matched.node child).2.2.1, List.length_map] at lengths
    omega


/-- Finished original source nodes have already published every channel in
all of their completed descendants, so stale paths add no new scope labels. -/
private theorem completed_scope_covered (graph : DAG n) (logical : DFSState graph)
    (channels : List (Channel n))
    (published : ∀ node ∈ logical.completed, ∀ channel ∈ (graph.node node).directChannels,
      channel ∈ channels)
    (node : Fin graph.nodeCount) (member : node ∈ logical.completed)
    (channel : Channel n) (included : channel ∈ graph.scope node) : channel ∈ channels := by
  rw [graph.scope_eq] at included
  rcases Finset.mem_union.mp included with direct | descendant
  · exact published node member channel (List.mem_toFinset.mp direct)
  · obtain ⟨child, childMember, inChild⟩ := Finset.mem_biUnion.mp descendant
    exact completed_scope_covered graph logical channels published (graph.childIndex node child)
      (logical.closed node member child (List.mem_toFinset.mp childMember)) channel inChild
termination_by node.val
decreasing_by exact graph.childIndex_lt node child

/-- Appending a source node after all original child occurrences have finished
preserves the actual postorder, including repeated child IDs. -/
private theorem postorder_append_node (graph : DAG n)
    (before : List (Fin graph.nodeCount)) (node : Fin graph.nodeCount)
    (ordered : Postorder graph before) (fresh : node ∉ before)
    (childrenDone : ∀ child ∈ (graph.node node).children,
      graph.childIndex node child ∈ before) : Postorder graph (before ++ [node]) := by
  refine ⟨?_, ?_⟩
  · rw [List.nodup_append_comm]
    exact List.nodup_cons.mpr ⟨fresh, ordered.1⟩
  · intro position
    change ∀ child : Fin ((before ++ [node])[position.val]'position.isLt).val,
      child ∈ (graph.node ((before ++ [node])[position.val]'position.isLt)).children →
      graph.childIndex ((before ++ [node])[position.val]'position.isLt) child ∈
        (before ++ [node]).take position.val
    generalize fetchedEq : (before ++ [node])[position.val]'position.isLt = fetchedNode
    by_cases earlier : position.val < before.length
    · have entry : (before ++ [node])[position.val]'position.isLt = before[position.val]'earlier := by
        change (before ++ [node])[position.val]'position.isLt = before[position.val]'earlier
        exact List.getElem_append_left earlier
      rw [entry] at fetchedEq
      subst fetchedNode
      intro child member
      have seen := ordered.2 ⟨position.val, earlier⟩ child member
      simpa only [Fin.getElem_fin, List.take_append_of_le_length (Nat.le_of_lt earlier)] using seen
    · have lastPosition : position.val = before.length := by
        have := position.isLt
        simp only [List.length_append, List.length_singleton] at this
        omega
      have entry : (before ++ [node])[position.val]'position.isLt = node := by
        change (before ++ [node])[position.val]'position.isLt = node
        rw [List.getElem_append_right (by omega)]
        simp only [lastPosition, Nat.sub_self, List.getElem_cons_zero]
      rw [entry] at fetchedEq
      subst fetchedNode
      intro child member
      have takeBefore : (before ++ [node]).take position.val = before := by
        rw [lastPosition, List.take_left]
      rw [takeBefore]
      exact childrenDone child member


private def child_slice_empty (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width)) (base arityBase directory : Nat)
    (code : ChildCodeAt program layout base arityBase directory)
    (current : Fin graph.nodeCount) (initial : State width 8)
    (before : DFSState graph) (channels : List (Channel n)) (cursor : Nat)
    (stored : TraversalStored graph layout source initial before channels)
    (position : initial.pc = word width (base + 28)) (running : initial.halted = false)
    (count : initial.reg 4 = word width 0) (cursorHeld : initial.reg 6 = word width cursor) :
    ChildSliceTrace program graph layout source base current [] cursor initial before channels := by
  let final : State width 8 := { initial.advance with pc := word width (base + 47) }
  have trace : Execution program initial final 1 initial.liveWords := by
    simpa only [final, ite_true] using
      streamTest_execution program initial (base + 28) (base + 47) 0 code.test
        position running (by have := code.fits; omega) (by have := code.fits; omega) count
  refine {
    final := final, logical := before, channels := channels, ticks := 1,
    peak := initial.liveWords, execution := trace, charged := ?_, space := by omega,
    deltaSpace := by simp,
    stored := {
      sourceRetained := stored.sourceRetained
      nodeDimension := stored.nodeDimension
      channelDimension := stored.channelDimension
      allocation := stored.allocation
      completed := stored.completed
      channelLedger := stored.channelLedger
      channelsUnique := stored.channelsUnique
      flags := stored.flags
      completedScope := stored.completedScope
      depth := stored.depth
      zero := stored.zero
      one := stored.one }, active := rfl, completed := rfl, addedPrefix := ?_,
    childDone := ?_, inside := ?_, channelsExact := ?_, postorder := fun ordered => ordered,
    values := fun address below => rfl, stack := rfl, output := rfl,
    count := count, cursorFinal := ?_, depth := rfl, zero := rfl, one := rfl,
    position := rfl, running := running }
  · simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
    omega
  · exact ⟨[], (List.append_nil _).symm⟩
  · intro child absent
    exact False.elim (List.not_mem_nil absent)
  · intro node member
    exact Or.inl member
  · intro channel
    simp only [List.not_mem_nil, false_and, exists_false, or_false]
  · change initial.reg 6 = word width (cursor + 0)
    simpa only [Nat.add_zero] using cursorHeld


/-- The stale branch consumes the actual source occurrence and restores the
same logical completion ledger; its marker lookup is derived from storage. -/
private theorem child_stale_global (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width)) (base arityBase directory : Nat)
    (code : ChildCodeAt program layout base arityBase directory)
    (initial : State width 8) (logical : DFSState graph) (channels : List (Channel n))
    (child : Fin graph.nodeCount) (cursor remaining : Nat)
    (stored : TraversalStored graph layout source initial logical channels)
    (member : child ∈ logical.completed) (storageFits : layout.storageEnd < 2 ^ width)
    (position : initial.pc = word width (base + 29)) (running : initial.halted = false)
    (cursorFits : cursor + 1 < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorHeld : initial.reg 6 = word width cursor)
    (countHeld : initial.reg 4 = word width (remaining + 1))
    (sourceBound : cursor < initial.heap.size)
    (sourceCell : initial.heap[cursor]'sourceBound = word width child.val) :
    ∃ final, Execution program initial final 16 (initial.liveWords + 2) ∧
      TraversalStored graph layout source final logical channels ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 2 = initial.reg 2 ∧ final.reg 3 = initial.reg 3 ∧
      final.reg 7 = initial.reg 7 ∧ final.heap = initial.heap ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.pc = word width (base + 28) ∧ final.halted = false := by
  have markerBelow : layout.nodeMarkerBase + child.val < layout.storageEnd := by
    have childBound := child.isLt
    have layoutBound : child.val < layout.nodeCount := by simpa only [stored.nodeDimension] using childBound
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have markerBound : layout.nodeMarkerBase + child.val < initial.heap.size := by
    rw [stored.allocation]
    exact markerBelow
  have marker : initial.heap[layout.nodeMarkerBase + child.val]'markerBound = word width 1 := by
    have cell := stored.flags child
    simp only [member, true_or, ite_true] at cell
    rw [Array.getElem?_eq_getElem markerBound] at cell
    exact Option.some.inj cell
  have flagNonzero : (word width 1).val ≠ 0 := by
    have oneFits : 1 < 2 ^ width := by have := code.fits; omega
    change 1 % 2 ^ width ≠ 0
    rw [Nat.mod_eq_of_lt oneFits]
    omega
  obtain ⟨final, trace, finalCount, finalCursor, finalZero, finalOne, finalDepth,
    finalHeap, finalStack, finalOutput, finalPosition, finalRunning⟩ :=
    child_stale_execution program initial (base + 29) (base + 18) (base + 41)
      (base + 28) layout.nodeMarkerBase cursor child.val remaining (word width 1)
      code.suspend
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using code.touch)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using code.dispatchFresh)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using code.dispatchStale)
      code.resumeCodeAt position running (by have := code.fits; omega)
      (by have := code.fits; omega) (by have := code.fits; omega)
      cursorFits countFits cursorHeld countHeld stored.zero stored.one sourceBound sourceCell
      (by omega) markerBound marker flagNonzero
  refine ⟨final, trace, ?_, finalCount, finalCursor, finalZero, finalOne, finalDepth,
    finalHeap, finalStack, finalOutput, finalPosition, finalRunning⟩
  exact {
    sourceRetained := by simpa only [finalHeap] using stored.sourceRetained
    nodeDimension := stored.nodeDimension
    channelDimension := stored.channelDimension
    allocation := by simpa only [finalHeap] using stored.allocation
    completed := by simpa only [finalHeap] using stored.completed
    channelLedger := by simpa only [finalHeap] using stored.channelLedger
    channelsUnique := stored.channelsUnique
    flags := by simpa only [finalHeap] using stored.flags
    completedScope := stored.completedScope
    depth := finalDepth.trans stored.depth
    zero := finalZero.trans stored.zero
    one := finalOne.trans stored.one }


/-- Composition rule used by the physical slice induction. The first trace is
its fetched test plus stale branch, and the tail is the induction hypothesis
on the cursor advanced by that same trace. -/
private noncomputable def child_slice_stale_cons (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width)) (base : Nat)
    (current : Fin graph.nodeCount) (child : Fin current.val) (rest : List (Fin current.val))
    (cursor : Nat) (initial skipped : State width 8) (before : DFSState graph)
    (channels : List (Channel n))
    (member : graph.childIndex current child ∈ before.completed)
    (stored : TraversalStored graph layout source initial before channels)
    (first : Execution program initial skipped 17 (initial.liveWords + 2))
    (heap : skipped.heap = initial.heap) (stack : skipped.stack = initial.stack)
    (output : skipped.output = initial.output) (depth : skipped.reg 7 = initial.reg 7)
    (zero : skipped.reg 2 = initial.reg 2) (one : skipped.reg 3 = initial.reg 3)
    (tailTrace : ChildSliceTrace program graph layout source base current rest
      (cursor + 1) skipped before channels) :
    ChildSliceTrace program graph layout source base current (child :: rest)
      cursor initial before channels := by
  have sameLive : skipped.liveWords = initial.liveWords := by
    simp only [State.liveWords, heap, stack, output]
  let added := Classical.choose tailTrace.addedPrefix
  have appended := Classical.choose_spec tailTrace.addedPrefix
  have oldMember : graph.childIndex current child ∈ tailTrace.logical.completed := by
    rw [appended]
    exact List.mem_append_left added member
  refine {
    final := tailTrace.final, logical := tailTrace.logical, channels := tailTrace.channels,
    ticks := 17 + tailTrace.ticks, peak := max (initial.liveWords + 2) tailTrace.peak,
    execution := first.append tailTrace.execution, charged := ?_, space := ?_,
    deltaSpace := by
      have bound := tailTrace.deltaSpace
      rw [sameLive] at bound
      exact max_le (by omega) bound,
    stored := tailTrace.stored, active := tailTrace.active, completed := ?_,
    addedPrefix := ⟨added, appended⟩, childDone := ?_, inside := tailTrace.inside,
    channelsExact := ?_, postorder := tailTrace.postorder,
    values := ?_, stack := tailTrace.stack.trans stack, output := tailTrace.output.trans output,
    count := tailTrace.count, cursorFinal := ?_, depth := tailTrace.depth.trans depth,
    zero := tailTrace.zero.trans zero, one := tailTrace.one.trans one,
    position := tailTrace.position, running := tailTrace.running }
  · have charged := tailTrace.charged
    simp only [List.length_cons]
    omega
  · have space := tailTrace.space
    rw [sameLive] at space
    exact max_le (by omega) space
  · have seen : discoverNode graph (graph.childIndex current child) before.completed = before.completed := by
      rw [discoverNode]
      exact ite_eq_left member
    rw [List.foldl_cons, seen]
    exact tailTrace.completed
  · intro candidate belongs
    rcases List.mem_cons.mp belongs with same | remaining
    · subst candidate
      exact oldMember
    · exact tailTrace.childDone candidate remaining
  · intro channel
    rw [tailTrace.channelsExact]
    constructor
    · intro covered
      rcases covered with old | ⟨candidate, belongs, supported⟩
      · exact Or.inl old
      · exact Or.inr ⟨candidate, List.mem_cons_of_mem child belongs, supported⟩
    · intro covered
      rcases covered with old | ⟨candidate, belongs, supported⟩
      · exact Or.inl old
      · rcases List.mem_cons.mp belongs with same | remaining
        · subst candidate
          exact Or.inl (completed_scope_covered graph before channels stored.completedScope
            (graph.childIndex current child) member channel supported)
        · exact Or.inr ⟨candidate, remaining, supported⟩
  · intro address below
    exact (tailTrace.values address below).trans (by rw [heap])
  · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 rest.length] using
      tailTrace.cursorFinal


/-- The slice recursion carries its position in the original row, rather than
allowing an arbitrary list of represented child IDs to replace that row. -/
private structure OriginalChildSuffix (graph : DAG n) (current : Fin graph.nodeCount)
    (originalCursor cursor : Nat) (remaining : List (Fin current.val)) where
  consumed : List (Fin current.val)
  row : (graph.node current).children = consumed ++ remaining
  position : cursor = originalCursor + consumed.length

private def original_child_suffix_tail (graph : DAG n) (current : Fin graph.nodeCount)
    (originalCursor cursor : Nat) (child : Fin current.val) (rest : List (Fin current.val))
    (suffix : OriginalChildSuffix graph current originalCursor cursor (child :: rest)) :
    OriginalChildSuffix graph current originalCursor (cursor + 1) rest := by
  refine ⟨suffix.consumed ++ [child], ?_, ?_⟩
  · rw [suffix.row, List.append_assoc]
    rfl
  · simp only [List.length_append, List.length_singleton]
    have position := suffix.position
    omega

private theorem original_child_suffix_member (graph : DAG n) (current : Fin graph.nodeCount)
    (originalCursor cursor : Nat) (child : Fin current.val) (rest : List (Fin current.val))
    (suffix : OriginalChildSuffix graph current originalCursor cursor (child :: rest)) :
    child ∈ (graph.node current).children := by
  rw [suffix.row]
  exact List.mem_append_right suffix.consumed (List.mem_cons_self)


/-- The caller's actual test, enter and completion cost is paid by one newly
finished node and the one represented parent incidence, without charging the
ambient node or channel dimensions per query. -/
private theorem fresh_branch_charge (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width)) (base : Nat)
    (child : Fin graph.nodeCount) (entered : State width 8)
    (before : DFSState graph) (channels : List (Channel n))
    (body : NodeBodyTrace program graph layout source base child entered before channels) :
    45 + body.ticks + 46 * freshWeight graph before.completed ≤
      46 * freshWeight graph (body.logical.completed ++ [child]) + 17 := by
  have charged := body.charged
  have singleton : freshWeight graph [child] = localNodeWeight graph child := by
    simp only [freshWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [freshWeight_append, singleton]
  dsimp only [localNodeWeight]
  omega

private theorem child_ancestors_above (graph : DAG n) (current : Fin graph.nodeCount)
    (child : Fin current.val) (ancestors : List (Fin graph.nodeCount))
    (above : AncestorsAbove graph current ancestors) :
    AncestorsAbove graph (graph.childIndex current child) (current :: ancestors) := by
  intro ancestor belongs
  have earlier := graph.childIndex_lt current child
  rcases List.mem_cons.mp belongs with same | old
  · subst ancestor
    exact earlier
  · have later := above ancestor old
    omega


private theorem child_stale_test (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width)) (base arityBase directory : Nat)
    (code : ChildCodeAt program layout base arityBase directory)
    (initial : State width 8) (logical : DFSState graph) (channels : List (Channel n))
    (child : Fin graph.nodeCount) (cursor remaining : Nat)
    (stored : TraversalStored graph layout source initial logical channels)
    (member : child ∈ logical.completed) (storageFits : layout.storageEnd < 2 ^ width)
    (position : initial.pc = word width (base + 28)) (running : initial.halted = false)
    (cursorFits : cursor + 1 < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorHeld : initial.reg 6 = word width cursor)
    (countHeld : initial.reg 4 = word width (remaining + 1))
    (sourceBound : cursor < initial.heap.size)
    (sourceCell : initial.heap[cursor]'sourceBound = word width child.val) :
    ∃ final, Execution program initial final 17 (initial.liveWords + 2) ∧
      TraversalStored graph layout source final logical channels ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 2 = initial.reg 2 ∧ final.reg 3 = initial.reg 3 ∧
      final.reg 7 = initial.reg 7 ∧ final.heap = initial.heap ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.pc = word width (base + 28) ∧ final.halted = false := by
  let tested : State width 8 := initial.advance
  have first : Execution program initial tested 1 initial.liveWords := by
    simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, tested] using
      streamTest_execution program initial (base + 28) (base + 47) (remaining + 1)
        code.test position running (by have := code.fits; omega) countFits countHeld
  have testedPosition : tested.pc = word width (base + 29) := by
    have entryFits : base + 28 < 2 ^ width := by have := code.fits; omega
    have entryVal : (word width (base + 28)).val = base + 28 := Nat.mod_eq_of_lt entryFits
    change word width (initial.pc.val + 1) = word width (base + 29)
    rw [position, entryVal]
  have testedStored : TraversalStored graph layout source tested logical channels := {
    sourceRetained := stored.sourceRetained
    nodeDimension := stored.nodeDimension
    channelDimension := stored.channelDimension
    allocation := stored.allocation
    completed := stored.completed
    channelLedger := stored.channelLedger
    channelsUnique := stored.channelsUnique
    flags := stored.flags
    completedScope := stored.completedScope
    depth := stored.depth
    zero := stored.zero
    one := stored.one }
  obtain ⟨final, second, finalStored, finalCount, finalCursor, finalZero, finalOne,
    finalDepth, finalHeap, finalStack, finalOutput, finalPosition, finalRunning⟩ :=
    child_stale_global program graph layout source base arityBase directory code tested logical
      channels child cursor remaining testedStored member storageFits testedPosition running
      cursorFits countFits cursorHeld countHeld sourceBound sourceCell
  refine ⟨final, ?_, finalStored, finalCount, finalCursor, finalZero, finalOne,
    finalDepth, finalHeap, finalStack, finalOutput, finalPosition, finalRunning⟩
  have trace := first.append second
  have sameLive : tested.liveWords = initial.liveWords := rfl
  simpa only [sameLive, Nat.reduceAdd, Nat.max_eq_right (by omega :
    initial.liveWords ≤ initial.liveWords + 2)] using trace


/-- Internal fresh branch of the well-founded node-body induction. The supplied
body proof is the induction hypothesis for this strictly smaller source ID;
the caller executes completion and restores its saved parent continuation. -/
private theorem child_fresh_recursive (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width)) (base arityBase directory : Nat)
    (code : ChildCodeAt program layout base arityBase directory)
    (current : Fin graph.nodeCount) (childSlot : Fin current.val)
    (initial : State width 8) (before : DFSState graph) (channels : List (Channel n))
    (cursor remaining : Nat) (ancestors : List (Fin graph.nodeCount))
    (activeShape : before.active = current :: ancestors)
    (above : AncestorsAbove graph current ancestors)
    (fresh : graph.childIndex current childSlot ∉ before.completed)
    (metadata : ChildMetadata graph layout initial.heap arityBase directory
      (graph.childIndex current childSlot))
    (sourceSize : source.size = layout.sourceEnd)
    (stored : TraversalStored graph layout source initial before channels)
    (storageFits : layout.storageEnd < 2 ^ width)
    (depthFits : before.active.length + 1 < 2 ^ width)
    (position : initial.pc = word width (base + 29)) (running : initial.halted = false)
    (cursorFits : cursor + 1 < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorHeld : initial.reg 6 = word width cursor)
    (countHeld : initial.reg 4 = word width (remaining + 1))
    (sourceBound : cursor < initial.heap.size)
    (sourceCell : initial.heap[cursor]'sourceBound =
      word width (graph.childIndex current childSlot).val)
    (bodyIH : ∀ (entered : State width 8)
        (inactive : graph.childIndex current childSlot ∉ before.active),
      TraversalStored graph layout source entered
        (activateChild graph before (graph.childIndex current childSlot) fresh inactive) channels →
      entered.pc = word width (base + 28) → entered.halted = false →
      entered.reg 4 = word width (graph.node (graph.childIndex current childSlot)).children.length →
      entered.reg 6 = word width metadata.cursor →
      entered.stack = word width (graph.childIndex current childSlot).val :: word width cursor ::
        word width (remaining + 1) :: initial.stack →
      NodeBodyTrace program graph layout source base (graph.childIndex current childSlot)
        entered (activateChild graph before (graph.childIndex current childSlot) fresh inactive) channels) :
    ∃ (entered : State width 8)
      (inactive : graph.childIndex current childSlot ∉ before.active)
      (body : NodeBodyTrace program graph layout source base (graph.childIndex current childSlot)
        entered (activateChild graph before (graph.childIndex current childSlot) fresh inactive) channels)
      (returned : State width 8)
      (shape : body.logical.active = graph.childIndex current childSlot :: before.active),
      entered.liveWords = initial.liveWords + 3 ∧
      Execution program initial returned (20 + body.ticks + 24)
        (max (initial.liveWords + 3) body.peak) ∧
      TraversalStored graph layout source returned
        (completeLogical graph body.logical (graph.childIndex current childSlot) before.active
          shape body.childDone) body.channels ∧
      (∀ address, address < layout.nodeMarkerBase → returned.heap[address]? = initial.heap[address]?) ∧
      returned.stack = initial.stack ∧ returned.output = initial.output ∧
      returned.reg 4 = word width remaining ∧ returned.reg 6 = word width (cursor + 1) ∧
      returned.pc = word width (base + 28) ∧ returned.halted = false := by
  let child := graph.childIndex current childSlot
  have inactive : child ∉ before.active := by
    intro seen
    have completed := marked_child_completed graph current childSlot before.completed ancestors
      above (Or.inr (by simpa only [activeShape] using seen))
    exact fresh completed
  obtain ⟨entered, enterTrace, enterStored, enterValues, enterStack, enterOutput,
    enterCount, enterCursor, enterPosition, enterRunning⟩ :=
    child_fresh_global program graph layout source before initial channels child fresh inactive
      (base + 29) (base + 18) cursor remaining arityBase directory
      (graph.node child).children.length metadata.cursor code.suspend
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using code.touch)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using code.dispatchFresh)
      code.enterCodeAt sourceSize stored position running (by have := code.fits; omega)
      (by have := code.fits; omega) storageFits depthFits cursorHeld countHeld sourceBound
      sourceCell metadata.arityBound metadata.directoryBound metadata.arityBeforeMarker
      metadata.directoryBeforeMarker metadata.arity metadata.directory
  have body := bodyIH entered inactive enterStored
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using enterPosition) enterRunning enterCount enterCursor enterStack
  have shape : body.logical.active = child :: before.active := body.active
  have bodyStack : body.final.stack = word width child.val :: word width cursor ::
      word width (remaining + 1) :: initial.stack := body.stack.trans enterStack
  obtain ⟨returned, returnTrace, returnStored, returnValues, returnStack, returnOutput,
    returnCount, returnCursor, returnPosition, returnRunning⟩ :=
    complete_child_global program graph layout source body.logical body.final body.channels child
      before.active (base + 96) (base + 41) (base + 28) (base + 114) cursor remaining initial.stack
      code.finishCodeAt
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using code.returnCodeAt)
      code.resumeCodeAt sourceSize body.stored shape
      (by rw [activeShape]; simp only [List.length_cons]; omega)
      body.childDone body.ownScope body.position body.running (by have := code.fits; omega)
      (by have := code.fits; omega) (by have := code.fits; omega) storageFits depthFits
      cursorFits countFits bodyStack
  have enteredLive : entered.liveWords = initial.liveWords + 3 := by
    simp only [State.liveWords, enterStored.allocation, stored.allocation, enterStack, enterOutput,
      List.length_cons]
    omega
  have bodyFinalLive : body.final.liveWords = entered.liveWords := by
    simp only [State.liveWords, body.stored.allocation, enterStored.allocation, body.stack, body.output]
  have bodyPeak : entered.liveWords ≤ body.peak := body.execution.initial_storage_le
  refine ⟨entered, inactive, body, returned, shape, enteredLive, ?_, returnStored, ?_, returnStack,
    returnOutput.trans (body.output.trans enterOutput), returnCount, returnCursor,
    returnPosition, returnRunning⟩
  · have trace := (enterTrace.append body.execution).append returnTrace
    have peakEq : max (max (initial.liveWords + 3) body.peak) body.final.liveWords =
        max (initial.liveWords + 3) body.peak := by
      rw [bodyFinalLive, enteredLive]
      omega
    simpa only [peakEq] using trace
  · intro address below
    exact (returnValues address below).trans ((body.values address below).trans (enterValues address below))


private noncomputable def child_slice_fresh_cons (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width)) (base : Nat)
    (current : Fin graph.nodeCount) (childSlot : Fin current.val) (rest : List (Fin current.val))
    (cursor : Nat) (initial entered returned : State width 8) (before : DFSState graph)
    (channels : List (Channel n))
    (initialStored : TraversalStored graph layout source initial before channels)
    (fresh : graph.childIndex current childSlot ∉ before.completed)
    (inactive : graph.childIndex current childSlot ∉ before.active)
    (childMember : childSlot ∈ (graph.node current).children)
    (body : NodeBodyTrace program graph layout source base (graph.childIndex current childSlot)
      entered (activateChild graph before (graph.childIndex current childSlot) fresh inactive) channels)
    (shape : body.logical.active = graph.childIndex current childSlot :: before.active)
    (enteredLive : entered.liveWords = initial.liveWords + 3)
    (first : Execution program initial returned (45 + body.ticks)
      (max (initial.liveWords + 3) body.peak))
    (firstSpace : max (initial.liveWords + 3) body.peak ≤ initial.liveWords + 3 * current.val + 3)
    (firstValues : ∀ address, address < layout.nodeMarkerBase → returned.heap[address]? = initial.heap[address]?)
    (stack : returned.stack = initial.stack) (output : returned.output = initial.output)
    (allocation : returned.heap.size = initial.heap.size)
    (tailTrace : ChildSliceTrace program graph layout source base current rest (cursor + 1) returned
      (completeLogical graph body.logical (graph.childIndex current childSlot) before.active shape body.childDone)
      body.channels) :
    ChildSliceTrace program graph layout source base current (childSlot :: rest)
      cursor initial before channels := by
  let child := graph.childIndex current childSlot
  let middle := completeLogical graph body.logical child before.active shape body.childDone
  let descendants := Classical.choose body.addedPrefix
  have bodyAppended : body.logical.completed = before.completed ++ descendants :=
    Classical.choose_spec body.addedPrefix
  let after := Classical.choose tailTrace.addedPrefix
  have tailAppended : tailTrace.logical.completed = middle.completed ++ after :=
    Classical.choose_spec tailTrace.addedPrefix
  have middleCompleted : middle.completed = before.completed ++ (descendants ++ [child]) := by
    change body.logical.completed ++ [child] = _
    exact (congrArg (fun nodes => nodes ++ [child]) bodyAppended).trans
      (List.append_assoc before.completed descendants [child])
  have appended : tailTrace.logical.completed = before.completed ++ ((descendants ++ [child]) ++ after) := by
    exact tailAppended.trans ((congrArg (fun nodes => nodes ++ after) middleCompleted).trans
      (List.append_assoc before.completed (descendants ++ [child]) after))
  have oldMember : child ∈ tailTrace.logical.completed := by
    rw [tailAppended]
    apply List.mem_append_left
    change child ∈ body.logical.completed ++ [child]
    exact List.mem_append_right _ (List.mem_singleton_self child)
  have sameLive : returned.liveWords = initial.liveWords := by
    simp only [State.liveWords, allocation, stack, output]
  have insideMiddle : ∀ node ∈ middle.completed, node ∈ before.completed ∨ node ∈ graph.cone current := by
    intro node member
    change node ∈ body.logical.completed ++ [child] at member
    rcases List.mem_append.mp member with old | last
    · rcases body.inside node old with original | descendant
      · exact Or.inl original
      · exact Or.inr (graph.cone_child_subset current childSlot childMember descendant)
    · have same : node = child := List.mem_singleton.mp last
      subst node
      exact Or.inr (graph.cone_child_subset current childSlot childMember (graph.self_mem_cone child))
  refine {
    final := tailTrace.final, logical := tailTrace.logical, channels := tailTrace.channels,
    ticks := (45 + body.ticks) + tailTrace.ticks,
    peak := max (max (initial.liveWords + 3) body.peak) tailTrace.peak,
    execution := first.append tailTrace.execution, charged := ?_, space := ?_,
    deltaSpace := by
      have beforeLength : before.completed.length ≤ body.logical.completed.length := by
        have lengths := congrArg List.length bodyAppended
        simp only [List.length_append] at lengths
        omega
      have afterLength : body.logical.completed.length + 1 ≤ tailTrace.logical.completed.length := by
        have lengths := congrArg List.length tailAppended
        simp only [middle, completeLogical, List.length_append,
          List.length_singleton] at lengths
        omega
      have bodyBound := body.deltaSpace
      change body.peak ≤ entered.liveWords +
        3 * (body.logical.completed.length - before.completed.length) + 3 at bodyBound
      rw [enteredLive] at bodyBound
      have tailBound := tailTrace.deltaSpace
      simp only [completeLogical, List.length_append, List.length_singleton] at tailBound
      rw [sameLive] at tailBound
      exact fresh_space_telescope before.completed.length body.logical.completed.length
        tailTrace.logical.completed.length initial.liveWords body.peak tailTrace.peak
        beforeLength afterLength bodyBound tailBound,
    stored := tailTrace.stored, active := tailTrace.active, completed := ?_,
    addedPrefix := ⟨_, appended⟩, childDone := ?_, inside := ?_, channelsExact := ?_,
    postorder := ?_, values := ?_, stack := tailTrace.stack.trans stack,
    output := tailTrace.output.trans output, count := tailTrace.count, cursorFinal := ?_,
    depth := ?_, zero := ?_, one := ?_, position := tailTrace.position, running := tailTrace.running }
  · have firstCharge := fresh_branch_charge program graph layout source base child entered
      (activateChild graph before child fresh inactive) channels body
    have tailCharge := tailTrace.charged
    change tailTrace.ticks + 46 * freshWeight graph (body.logical.completed ++ [child]) ≤
      46 * freshWeight graph tailTrace.logical.completed + 17 * rest.length + 1 at tailCharge
    change 45 + body.ticks + 46 * freshWeight graph before.completed ≤
      46 * freshWeight graph (body.logical.completed ++ [child]) + 17 at firstCharge
    simp only [List.length_cons]
    omega
  · have tailSpace := tailTrace.space
    rw [sameLive] at tailSpace
    exact max_le firstSpace tailSpace
  · rw [tailTrace.completed]
    change rest.foldl (fun done candidate => discoverNode graph (graph.childIndex current candidate) done)
      (body.logical.completed ++ [child]) = _
    rw [List.foldl_cons, discoverNode, ite_eq_right fresh]
    rw [body.completed]
    rfl
  · intro candidate member
    rcases List.mem_cons.mp member with same | remaining
    · subst candidate
      exact oldMember
    · exact tailTrace.childDone candidate remaining
  · intro node member
    rcases tailTrace.inside node member with prior | descendant
    · exact insideMiddle node prior
    · exact Or.inr descendant
  · intro channel
    rw [tailTrace.channelsExact, body.channelsExact]
    constructor
    · intro covered
      rcases covered with (old | childScope) | ⟨candidate, member, scopeMember⟩
      · exact Or.inl old
      · exact Or.inr ⟨childSlot, List.mem_cons_self, childScope⟩
      · exact Or.inr ⟨candidate, List.mem_cons_of_mem _ member, scopeMember⟩
    · intro covered
      rcases covered with old | ⟨candidate, member, scopeMember⟩
      · exact Or.inl (Or.inl old)
      · rcases List.mem_cons.mp member with same | remaining
        · subst candidate
          exact Or.inl (Or.inr scopeMember)
        · exact Or.inr ⟨candidate, remaining, scopeMember⟩
  · intro ordered
    apply tailTrace.postorder
    change Postorder graph (body.logical.completed ++ [child])
    have childFresh : child ∉ body.logical.completed :=
      (List.disjoint_cons_right.mp (shape ▸ body.logical.separate)).1
    exact postorder_append_node graph body.logical.completed child (body.postorder ordered)
      childFresh body.childDone
  · intro address below
    exact (tailTrace.values address below).trans (firstValues address below)
  · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 rest.length] using tailTrace.cursorFinal
  · rw [tailTrace.stored.depth, tailTrace.active]
    exact initialStored.depth.symm
  · exact tailTrace.stored.zero.trans initialStored.zero.symm
  · exact tailTrace.stored.one.trans initialStored.one.symm


/-- Prefix witnesses turn the actual stack recurrence into a fresh-node charge.
The parent continuation is counted once for the newly completed child. -/
private theorem directory_execution (program : Program width 8) (state : State width 8)
    (entry arityBase sourceBase offset count cursor : Nat)
    (present : ∀ phase : Fin 6, program[entry + phase.val]? =
      (directoryCode width arityBase sourceBase)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 6 < 2 ^ width) (held : state.reg 0 = word width offset)
    (arityFits : arityBase + offset < 2 ^ width) (sourceFits : sourceBase + offset < 2 ^ width)
    (arityBound : arityBase + offset < state.heap.size)
    (sourceBound : sourceBase + offset < state.heap.size)
    (arityCell : state.heap[arityBase + offset]'arityBound = word width count)
    (sourceCell : state.heap[sourceBase + offset]'sourceBound = word width cursor) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 4 = word width count ∧ final.reg 6 = word width cursor ∧
      (∀ register : Fin 8, register ≠ 1 → register ≠ 4 → register ≠ 6 →
        final.reg register = state.reg register) ∧
      final.pc = word width (entry + 6) ∧ final.halted = false := by
  let s1 := state.advance.put 1 (word width arityBase)
  let s2 := s1.advance.put 1 (word width (arityBase + offset))
  let s3 := s2.advance.put 4 (word width count)
  let s4 := s3.advance.put 1 (word width sourceBase)
  let s5 := s4.advance.put 1 (word width (sourceBase + offset))
  let final := s5.advance.put 6 (word width cursor)
  have arityVal : (word width arityBase).val = arityBase := Nat.mod_eq_of_lt (by omega)
  have sourceVal : (word width sourceBase).val = sourceBase := Nat.mod_eq_of_lt (by omega)
  have offsetVal : (word width offset).val = offset := Nat.mod_eq_of_lt (by omega)
  have arityAddress : (word width (arityBase + offset)).val = arityBase + offset := Nat.mod_eq_of_lt arityFits
  have sourceAddress : (word width (sourceBase + offset)).val = sourceBase + offset := Nat.mod_eq_of_lt sourceFits
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.put, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.constant 1 (word width arityBase))
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [directoryCode] using present ⟨0, by decide⟩)]
    simp [step, s1, s5, s4, s3, s2, s1, State.put, State.advance, running, held,
      arityVal, sourceVal, offsetVal, arityAddress, sourceAddress, arityBound, sourceBound,
      arityCell, sourceCell]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.put, State.advance, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.add 1 1 0)
      (by simpa only [Nat.add_zero] using p1) (by omega)
      (by simpa [directoryCode] using present ⟨1, by decide⟩)]
    simp [step, s2, s5, s4, s3, s2, s1, State.put, State.advance, running, held,
      arityVal, sourceVal, offsetVal, arityAddress, sourceAddress, arityBound, sourceBound,
      arityCell, sourceCell]
  have p3 : s3.pc = word width (entry + 3) := by
    simp only [s3, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.load 4 1)
      (by simpa only [Nat.add_zero] using p2) (by omega)
      (by simpa [directoryCode] using present ⟨2, by decide⟩)]
    simp [step, s3, s5, s4, s3, s2, s1, State.put, State.advance, running, held,
      arityVal, sourceVal, offsetVal, arityAddress, sourceAddress, arityBound, sourceBound,
      arityCell, sourceCell]
  have p4 : s4.pc = word width (entry + 4) := by
    simp only [s4, State.put, State.advance, p3]
    rw [show (word width (entry + 3)).val = entry + 3 from Nat.mod_eq_of_lt (by omega)]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.constant 1 (word width sourceBase))
      (by simpa only [Nat.add_zero] using p3) (by omega)
      (by simpa [directoryCode] using present ⟨3, by decide⟩)]
    simp [step, s4, s5, s4, s3, s2, s1, State.put, State.advance, running, held,
      arityVal, sourceVal, offsetVal, arityAddress, sourceAddress, arityBound, sourceBound,
      arityCell, sourceCell]
  have p5 : s5.pc = word width (entry + 5) := by
    simp only [s5, State.put, State.advance, p4]
    rw [show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (by omega)]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 1 1 0)
      (by simpa only [Nat.add_zero] using p4) (by omega)
      (by simpa [directoryCode] using present ⟨4, by decide⟩)]
    simp [step, s5, s5, s4, s3, s2, s1, State.put, State.advance, running, held,
      arityVal, sourceVal, offsetVal, arityAddress, sourceAddress, arityBound, sourceBound,
      arityCell, sourceCell]
  have p6 : final.pc = word width (entry + 6) := by
    simp only [final, State.put, State.advance, p5]
    rw [show (word width (entry + 5)).val = entry + 5 from Nat.mod_eq_of_lt (by omega)]
  have t5 : programStep program s5 = some final := by
    rw [fetched program s5 (entry + 5) (.load 6 1)
      (by simpa only [Nat.add_zero] using p5) (by omega)
      (by simpa [directoryCode] using present ⟨5, by decide⟩)]
    simp [step, final, s5, s4, s3, s2, s1, State.put, State.advance, running, held,
      arityVal, sourceVal, offsetVal, arityAddress, sourceAddress, arityBound, sourceBound,
      arityCell, sourceCell]
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, ?_, p6, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
      (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl final))))))
    have live1 : s1.liveWords = state.liveWords := rfl
    have live2 : s2.liveWords = state.liveWords := rfl
    have live3 : s3.liveWords = state.liveWords := rfl
    have live4 : s4.liveWords = state.liveWords := rfl
    have live5 : s5.liveWords = state.liveWords := rfl
    have live6 : final.liveWords = state.liveWords := rfl
    simpa only [live1, live2, live3, live4, live5, live6, Nat.max_self] using trace
  · simp [final, s5, s4, s3, s2, s1, State.put, State.advance]
  · simp [final, s5, s4, s3, s2, s1, State.put, State.advance]
  · intro register notOne notFour notSix
    simp [final, s5, s4, s3, s2, s1, State.put, State.advance, notOne, notFour, notSix]


private theorem input_scope_execution (program : Program width 8) (state : State width 8)
    (entry headBase offset : Nat)
    (present : ∀ phase : Fin 3, program[entry + phase.val]? =
      (inputScopeCode width headBase)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 3 < 2 ^ width) (held : state.reg 0 = word width offset)
    (headFits : headBase + offset < 2 ^ width) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 4 = word width 1 ∧ final.reg 6 = word width (headBase + offset) ∧
      (∀ register : Fin 8, register ≠ 4 → register ≠ 6 → final.reg register = state.reg register) ∧
      final.pc = word width (entry + 3) ∧ final.halted = false := by
  let s1 := state.advance.put 6 (word width headBase)
  let s2 := s1.advance.put 6 (word width (headBase + offset))
  let final := s2.advance.put 4 (word width 1)
  have baseVal : (word width headBase).val = headBase := Nat.mod_eq_of_lt (by omega)
  have offsetVal : (word width offset).val = offset := Nat.mod_eq_of_lt (by omega)
  have p1 : s1.pc = word width (entry + 1) := by
    simp only [s1, State.put, State.advance, position]
    rw [show (word width entry).val = entry from Nat.mod_eq_of_lt (by omega)]
  have p2 : s2.pc = word width (entry + 2) := by
    simp only [s2, State.put, State.advance, p1]
    rw [show (word width (entry + 1)).val = entry + 1 from Nat.mod_eq_of_lt (by omega)]
  have p3 : final.pc = word width (entry + 3) := by
    simp only [final, State.put, State.advance, p2]
    rw [show (word width (entry + 2)).val = entry + 2 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry (.constant 6 (word width headBase)) position (by omega)
      (by simpa [inputScopeCode] using present ⟨0, by decide⟩)]
    simp [step, s1, running]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.add 6 6 0) p1 (by omega)
      (by simpa [inputScopeCode] using present ⟨1, by decide⟩)]
    simp [step, s2, s1, State.put, State.advance, running, held, baseVal, offsetVal]
  have t2 : programStep program s2 = some final := by
    rw [fetched program s2 (entry + 2) (.constant 4 (word width 1)) p2 (by omega)
      (by simpa [inputScopeCode] using present ⟨2, by decide⟩)]
    simp [step, final, s2, s1, State.put, State.advance, running]
  refine ⟨final, ?_, rfl, rfl, rfl, ?_, ?_, ?_, p3, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl final)))
    have live1 : s1.liveWords = state.liveWords := rfl
    have live2 : s2.liveWords = state.liveWords := rfl
    have live3 : final.liveWords = state.liveWords := rfl
    simpa only [live1, live2, live3, Nat.max_self] using trace
  · simp [final, s2, s1, State.put, State.advance]
  · simp [final, s2, s1, State.put, State.advance]
  · intro register notFour notSix
    simp [final, s2, s1, State.put, State.advance, notFour, notSix]

private theorem zero_jump_execution (program : Program width 8) (state : State width 8)
    (entry target : Nat) (present : program[entry]? = some (.branchZero 2 (word width target)))
    (position : state.pc = word width entry) (running : state.halted = false)
    (fits : entry < 2 ^ width) (zero : state.reg 2 = word width 0) :
    Execution program state { state.advance with pc := word width target } 1 state.liveWords := by
  have transition : programStep program state = some { state.advance with pc := word width target } := by
    rw [fetched program state entry (.branchZero 2 (word width target)) position fits present]
    simp [step, running, zero, word]
  have sameLive : ({ state.advance with pc := word width target } : State width 8).liveWords = state.liveWords := rfl
  simpa only [sameLive, Nat.max_self] using Execution.cons transition (Execution.refl _)


/-- Read-only scope preparation preserves every physical DFS store. Only the
three invariant registers need explicit projection equalities. -/
private theorem traversal_readonly (graph : DAG n) (layout : SharedLayout)
    (source : Array (Word width)) (before after : State width 8)
    (logical : DFSState graph) (channels : List (Channel n))
    (stored : TraversalStored graph layout source before logical channels)
    (heap : after.heap = before.heap)
    (depth : after.reg 7 = before.reg 7) (zero : after.reg 2 = before.reg 2)
    (one : after.reg 3 = before.reg 3) :
    TraversalStored graph layout source after logical channels := by
  refine {
    sourceRetained := ?_, nodeDimension := stored.nodeDimension,
    channelDimension := stored.channelDimension, allocation := ?_, completed := ?_,
    channelLedger := ?_, channelsUnique := stored.channelsUnique, flags := ?_,
    completedScope := stored.completedScope, depth := depth.trans stored.depth,
    zero := zero.trans stored.zero, one := one.trans stored.one }
  · rw [heap]; exact stored.sourceRetained
  · rw [heap]; exact stored.allocation
  · rw [heap]; exact stored.completed
  · rw [heap]; exact stored.channelLedger
  · rw [heap]; exact stored.flags

private structure ScopePreparationAt (program : Program width 8) (base tagBase headBase arityBase directory : Nat) : Prop where
  frame : ∀ phase : Fin 3, program[base + 47 + phase.val]? = nodeFrameCode[phase.val]?
  tag : ∀ phase : Fin 6, program[base + 50 + phase.val]? =
    (scopeTagCode width tagBase (base + 63))[phase.val]?
  guards : ∀ phase : Fin 6, program[base + 56 + phase.val]? =
    (directoryCode width arityBase directory)[phase.val]?
  guardJump : program[base + 62]? = some (.branchZero 2 (word width (base + 67)))
  input : ∀ phase : Fin 3, program[base + 63 + phase.val]? =
    (inputScopeCode width headBase)[phase.val]?
  inputJump : program[base + 66]? = some (.branchZero 2 (word width (base + 67)))
  fits : base + 120 < 2 ^ width

/-- The tag and directory portion does not allocate or replace any resident
source cell. It merely selects the original head singleton or guard slice. -/
private theorem scope_prepare_execution (program : Program width 8) (initial : State width 8)
    (base tagBase headBase arityBase directory identifier tag guardCount guardCursor : Nat)
    (suffix : List (Word width))
    (code : ScopePreparationAt program base tagBase headBase arityBase directory)
    (position : initial.pc = word width (base + 47)) (running : initial.halted = false)
    (zero : initial.reg 2 = word width 0)
    (stack : initial.stack = word width identifier :: suffix)
    (idFits : identifier < 2 ^ width) (tagFits : tag < 2 ^ width)
    (tagAddressFits : tagBase + 2 * identifier < 2 ^ width)
    (headAddressFits : headBase + 2 * identifier < 2 ^ width)
    (arityAddressFits : arityBase + 2 * identifier < 2 ^ width)
    (directoryAddressFits : directory + 2 * identifier < 2 ^ width)
    (tagBound : tagBase + 2 * identifier < initial.heap.size)
    (arityBound : arityBase + 2 * identifier < initial.heap.size)
    (directoryBound : directory + 2 * identifier < initial.heap.size)
    (tagCell : initial.heap[tagBase + 2 * identifier]'tagBound = word width tag)
    (arityCell : initial.heap[arityBase + 2 * identifier]'arityBound = word width guardCount)
    (directoryCell : initial.heap[directory + 2 * identifier]'directoryBound = word width guardCursor) :
    ∃ final ticks, Execution program initial final ticks initial.liveWords ∧ ticks ≤ 16 ∧
      final.heap = initial.heap ∧ final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 4 = word width (if tag = 1 then 1 else guardCount) ∧
      final.reg 6 = word width (if tag = 1 then headBase + 2 * identifier else guardCursor) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 4 → register ≠ 5 →
        register ≠ 6 → final.reg register = initial.reg register) ∧
      final.pc = word width (base + 67) ∧ final.halted = false := by
  obtain ⟨framed, frameTrace, frameHeap, frameStack, frameOutput, frameHeld, frameRegs,
    framePosition, frameRunning⟩ := nodeFrame_execution program initial (base + 47) identifier suffix
      code.frame position running (by have := code.fits; omega) idFits stack
  obtain ⟨tagged, tagTrace, tagHeap, tagStack, tagOutput, tagRegs, tagPosition, tagRunning⟩ :=
    scopeTag_execution program framed (base + 50) tagBase (base + 63) (2 * identifier) tag
      code.tag (by simpa only [Nat.add_assoc, Nat.reduceAdd] using framePosition) frameRunning
      (by have := code.fits; omega) frameHeld tagAddressFits tagFits
      (by simpa only [frameHeap] using tagBound) (by simpa only [frameHeap] using tagCell)
  have taggedLive : tagged.liveWords = initial.liveWords := by
    simp only [State.liveWords, tagHeap, frameHeap, tagStack, frameStack, tagOutput, frameOutput]
  have framedLive : framed.liveWords = initial.liveWords := by
    simp only [State.liveWords, frameHeap, frameStack, frameOutput]
  have taggedHeld : tagged.reg 0 = word width (2 * identifier) :=
    (tagRegs 0 (by decide) (by decide)).trans frameHeld
  have taggedZero : tagged.reg 2 = word width 0 :=
    (tagRegs 2 (by decide) (by decide)).trans ((frameRegs 2 (by decide)).trans zero)
  by_cases isInput : tag = 1
  · obtain ⟨prepared, prepTrace, prepHeap, prepStack, prepOutput, prepCount, prepCursor,
      prepRegs, prepPosition, prepRunning⟩ := input_scope_execution program tagged (base + 63)
        headBase (2 * identifier) code.input (by simpa only [isInput, ite_true] using tagPosition)
        tagRunning (by have := code.fits; omega) taggedHeld headAddressFits
    have prepZero := (prepRegs 2 (by decide) (by decide)).trans taggedZero
    let final : State width 8 := { prepared.advance with pc := word width (base + 67) }
    have jumpTrace := zero_jump_execution program prepared (base + 66) (base + 67)
      code.inputJump (by simpa only [Nat.add_assoc, Nat.reduceAdd] using prepPosition)
      prepRunning (by have := code.fits; omega) prepZero
    have jumpHeap : final.heap = prepared.heap := rfl
    have jumpStack : final.stack = prepared.stack := rfl
    have jumpOutput : final.output = prepared.output := rfl
    have jumpRegs : ∀ register, final.reg register = prepared.reg register := fun _ => rfl
    have finalPosition : final.pc = word width (base + 67) := rfl
    have finalRunning : final.halted = false := prepRunning
    have preparedLive : prepared.liveWords = initial.liveWords := by
      simp only [State.liveWords, prepHeap, tagHeap, frameHeap, prepStack, tagStack,
        frameStack, prepOutput, tagOutput, frameOutput]
    refine ⟨final, 13, ?_, by omega, jumpHeap.trans (prepHeap.trans (tagHeap.trans frameHeap)),
      jumpStack.trans (prepStack.trans (tagStack.trans frameStack)),
      jumpOutput.trans (prepOutput.trans (tagOutput.trans frameOutput)), ?_, ?_, ?_,
      finalPosition, finalRunning⟩
    · simpa only [framedLive, taggedLive, preparedLive, Nat.max_self, Nat.reduceAdd] using
        (((frameTrace.append tagTrace).append prepTrace).append jumpTrace)
    · simpa only [isInput, ite_true] using (jumpRegs 4).trans prepCount
    · simpa only [isInput, ite_true] using (jumpRegs 6).trans prepCursor
    · intro register not0 not1 not4 not5 not6
      exact (jumpRegs register).trans ((prepRegs register not4 not6).trans
        ((tagRegs register not1 not5).trans (frameRegs register not0)))
  · obtain ⟨prepared, prepTrace, prepHeap, prepStack, prepOutput, prepCount, prepCursor,
      prepRegs, prepPosition, prepRunning⟩ := directory_execution program tagged (base + 56)
        arityBase directory (2 * identifier) guardCount guardCursor code.guards
        (by simpa only [isInput, ite_false, Nat.add_assoc, Nat.reduceAdd] using tagPosition)
        tagRunning (by have := code.fits; omega) taggedHeld arityAddressFits directoryAddressFits
        (by simpa only [tagHeap, frameHeap] using arityBound)
        (by simpa only [tagHeap, frameHeap] using directoryBound)
        (by simpa only [tagHeap, frameHeap] using arityCell)
        (by simpa only [tagHeap, frameHeap] using directoryCell)
    have prepZero := (prepRegs 2 (by decide) (by decide) (by decide)).trans taggedZero
    let final : State width 8 := { prepared.advance with pc := word width (base + 67) }
    have jumpTrace := zero_jump_execution program prepared (base + 62) (base + 67)
      code.guardJump (by simpa only [Nat.add_assoc, Nat.reduceAdd] using prepPosition)
      prepRunning (by have := code.fits; omega) prepZero
    have jumpHeap : final.heap = prepared.heap := rfl
    have jumpStack : final.stack = prepared.stack := rfl
    have jumpOutput : final.output = prepared.output := rfl
    have jumpRegs : ∀ register, final.reg register = prepared.reg register := fun _ => rfl
    have finalPosition : final.pc = word width (base + 67) := rfl
    have finalRunning : final.halted = false := prepRunning
    have preparedLive : prepared.liveWords = initial.liveWords := by
      simp only [State.liveWords, prepHeap, tagHeap, frameHeap, prepStack, tagStack,
        frameStack, prepOutput, tagOutput, frameOutput]
    refine ⟨final, 16, ?_, by omega, jumpHeap.trans (prepHeap.trans (tagHeap.trans frameHeap)),
      jumpStack.trans (prepStack.trans (tagStack.trans frameStack)),
      jumpOutput.trans (prepOutput.trans (tagOutput.trans frameOutput)), ?_, ?_, ?_,
      finalPosition, finalRunning⟩
    · simpa only [framedLive, taggedLive, preparedLive, Nat.max_self, Nat.reduceAdd] using
        (((frameTrace.append tagTrace).append prepTrace).append jumpTrace)
    · simpa only [isInput, ite_false] using (jumpRegs 4).trans prepCount
    · simpa only [isInput, ite_false] using (jumpRegs 6).trans prepCursor
    · intro register not0 not1 not4 not5 not6
      exact (jumpRegs register).trans ((prepRegs register not1 not4 not6).trans
        ((tagRegs register not1 not5).trans (frameRegs register not0)))


/-- The active spine is a distinct source-ID list. Its increment fits the same
word capacity already required by the actual resident layout. -/
private theorem active_depth_fits (graph : DAG n) (layout : SharedLayout)
    (source : Array (Word width)) (state : State width 8) (logical : DFSState graph)
    (channels : List (Channel n))
    (stored : TraversalStored graph layout source state logical channels)
    (storageFits : layout.storageEnd < 2 ^ width) :
    logical.active.length + 1 < 2 ^ width := by
  have distinct := logical.activeUnique.length_le_card
  simp only [Fintype.card_fin] at distinct
  have dimension := stored.nodeDimension
  simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot,
    SharedLayout.nodeMarkerBase] at storageFits
  omega


/-- Scope preparation loads the immutable original tag and guard directory.
The guard endpoint is a serialized occurrence boundary, not a fresh list. -/
private structure RetainedScopeMetadata (graph : DAG n) (layout : SharedLayout)
    (heap caller : Array (Word width)) (rows : List ForestIndexedOperands.Row)
    (node : Fin graph.nodeCount) where
  tagBound : caller.size + 2 * node.val < heap.size
  arityBound : caller.size + 4 * rows.length + (2 * node.val + 1) < heap.size
  directoryBound : caller.size + 2 * rows.length + (2 * node.val + 1) < heap.size
  tagCell : heap[caller.size + 2 * node.val]'tagBound =
    word width (ForestIndexedOperands.tagValue graph node)
  arityCell : heap[caller.size + 4 * rows.length + (2 * node.val + 1)]'arityBound =
    word width (graph.node node).guardLabels.length
  directoryCell : heap[caller.size + 2 * rows.length + (2 * node.val + 1)]'directoryBound =
    word width (caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
      (ForestIndexedOperands.rowGuards (rows.take node.val)).length)
  guardEnd : caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
    (ForestIndexedOperands.rowGuards (rows.take node.val)).length +
    (graph.node node).guardLabels.length ≤ layout.nodeMarkerBase
  scope : ScopeStored heap
    (caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
      (ForestIndexedOperands.rowGuards (rows.take node.val)).length)
    (graph.node node).guardLabels

private def retained_scope_metadata (caller heap : Array (Word width)) (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (layout : SharedLayout)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (retained : CachePrefix heap (ForestIndexedOperands.cacheHeap width caller rows roots))
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (allocation : heap.size = layout.storageEnd) (node : Fin graph.nodeCount) :
    RetainedScopeMetadata graph layout heap caller rows node := by
  have valid : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
  have sourceBelowHeap : layout.sourceEnd < heap.size := by
    rw [allocation]
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase]
    omega
  have sourceBelowMarker : layout.sourceEnd ≤ layout.nodeMarkerBase := by
    simp only [SharedLayout.nodeMarkerBase]
    omega
  have tagSource : caller.size + 2 * node.val <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have aritySource : caller.size + 4 * rows.length + (2 * node.val + 1) <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have directorySource : caller.size + 2 * rows.length + (2 * node.val + 1) <
      (ForestIndexedOperands.cacheHeap width caller rows roots).size := by
    simp only [ForestIndexedOperands.cacheHeap_size]
    omega
  have tagBound : caller.size + 2 * node.val < heap.size := by
    rw [sourceSize] at tagSource
    omega
  have arityBound : caller.size + 4 * rows.length + (2 * node.val + 1) < heap.size := by
    rw [sourceSize] at aritySource
    omega
  have directoryBound : caller.size + 2 * rows.length + (2 * node.val + 1) < heap.size := by
    rw [sourceSize] at directorySource
    omega
  refine {
    tagBound := tagBound, arityBound := arityBound, directoryBound := directoryBound,
    tagCell := ?_, arityCell := ?_, directoryCell := ?_, guardEnd := ?_,
    scope := guard_scope_stored caller heap graph rows roots matched retained node }
  · have cell := retained ⟨_, tagSource⟩
    have original := ForestIndexedOperands.cache_tag_word caller graph rows roots matched node
    have exactCell := cell.trans (congrArg some original)
    rw [Array.getElem?_eq_getElem tagBound] at exactCell
    exact Option.some.inj exactCell
  · have cell := retained ⟨_, aritySource⟩
    have original := ForestIndexedOperands.cache_guard_arity_word caller graph rows roots matched node
    have exactCell := cell.trans (congrArg some original)
    rw [Array.getElem?_eq_getElem arityBound] at exactCell
    exact Option.some.inj exactCell
  · have cell := retained ⟨_, directorySource⟩
    have original := (ForestIndexedOperands.cache_base_words caller rows roots node.val valid).2
    have exactCell := cell.trans (congrArg some original)
    rw [Array.getElem?_eq_getElem directoryBound] at exactCell
    exact Option.some.inj exactCell
  · have lengths := congrArg List.length (ForestInputStored.row_guards_split rows node.val valid)
    simp only [List.length_append, (matched.node node).2.2.2, List.length_map] at lengths
    have sourceLength := sourceSize
    simp only [ForestIndexedOperands.cacheHeap_size] at sourceLength
    omega


private theorem dfs_suspend_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 2) :
    (dfsFromCache width caller rows roots base layout)[29 + phase.val]? =
      (suspendCode)[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem dfs_touch_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 8) :
    (dfsFromCache width caller rows roots base layout)[31 + phase.val]? =
      (touchCode width layout.nodeMarkerBase (base + 31))[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem dfs_enter_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 10) :
    (dfsFromCache width caller rows roots base layout)[18 + phase.val]? =
      (enterCode width (caller.size + 4 * rows.length) (caller.size + 2 * rows.length))[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem dfs_resume_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 6) :
    (dfsFromCache width caller rows roots base layout)[41 + phase.val]? =
      (resumeCode width (base + 28))[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem dfs_finish_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 13) :
    (dfsFromCache width caller rows roots base layout)[96 + phase.val]? =
      (finishLedgerCode width layout.nodeCountSlot layout.mapBase layout.nodeLedgerBase)[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem dfs_return_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 5) :
    (dfsFromCache width caller rows roots base layout)[109 + phase.val]? =
      (finishReturnCode width (base + 41) (base + 114))[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem dfs_frame_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 3) :
    (dfsFromCache width caller rows roots base layout)[47 + phase.val]? =
      (nodeFrameCode)[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem dfs_tag_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 6) :
    (dfsFromCache width caller rows roots base layout)[50 + phase.val]? =
      (scopeTagCode width caller.size (base + 63))[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem dfs_guards_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 6) :
    (dfsFromCache width caller rows roots base layout)[56 + phase.val]? =
      (directoryCode width (caller.size + 4 * rows.length + 1) (caller.size + 2 * rows.length + 1))[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem dfs_input_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 3) :
    (dfsFromCache width caller rows roots base layout)[63 + phase.val]? =
      (inputScopeCode width (caller.size + 1))[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem fixed_child_code
    (program : Program width 8) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout)
    (physical : ∀ phase : Fin 120, program[base + phase.val]? =
      (dfsFromCache width caller rows roots base layout)[phase.val]?)
    (fits : base + 120 < 2 ^ width) :
    ChildCodeAt program layout base (caller.size + 4 * rows.length)
      (caller.size + 2 * rows.length) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fits⟩

  · simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using physical ⟨28, by decide⟩

  · intro phase
    have cell := physical ⟨29 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_suspend_section caller rows roots base layout phase)

  · intro phase
    have cell := physical ⟨31 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_touch_section caller rows roots base layout phase)

  · simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using physical ⟨39, by decide⟩

  · simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using physical ⟨40, by decide⟩

  · intro phase
    have cell := physical ⟨18 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_enter_section caller rows roots base layout phase)

  · intro phase
    have cell := physical ⟨41 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_resume_section caller rows roots base layout phase)

  · intro phase
    have cell := physical ⟨96 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_finish_section caller rows roots base layout phase)

  · intro phase
    have cell := physical ⟨109 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_return_section caller rows roots base layout phase)

private theorem fixed_scope_preparation
    (program : Program width 8) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout)
    (physical : ∀ phase : Fin 120, program[base + phase.val]? =
      (dfsFromCache width caller rows roots base layout)[phase.val]?)
    (fits : base + 120 < 2 ^ width) :
    ScopePreparationAt program base caller.size (caller.size + 1)
      (caller.size + 4 * rows.length + 1) (caller.size + 2 * rows.length + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fits⟩

  · intro phase
    have cell := physical ⟨47 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_frame_section caller rows roots base layout phase)

  · intro phase
    have cell := physical ⟨50 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_tag_section caller rows roots base layout phase)

  · intro phase
    have cell := physical ⟨56 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_guards_section caller rows roots base layout phase)

  · simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using physical ⟨62, by decide⟩

  · intro phase
    have cell := physical ⟨63 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_input_section caller rows roots base layout phase)

  · simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using physical ⟨66, by decide⟩


private theorem scope_loop_framed (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width))
    (logical : DFSState graph) (state : State width 8) (channels labels : List (Channel n))
    (loop publish resume done cursor : Nat)
    (code : ScopeCodeAt program layout loop publish resume done)
    (storageFits : layout.storageEnd < 2 ^ width)
    (sourceBelow : source.size ≤ layout.channelMarkerBase)
    (stored : TraversalStored graph layout source state logical channels)
    (position : state.pc = word width loop) (running : state.halted = false)
    (countHeld : state.reg 4 = word width labels.length)
    (cursorHeld : state.reg 6 = word width cursor)
    (scopeEnd : cursor + labels.length ≤ layout.channelMarkerBase)
    (scope : ScopeStored state.heap cursor labels) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 27 * labels.length + 1 ∧ peak ≤ state.liveWords + 3 ∧
      TraversalStored graph layout source final logical (publishLabels channels labels) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 4 = word width 0 ∧ final.reg 6 = word width (cursor + labels.length) ∧
      final.pc = word width done ∧ final.halted = false ∧
      (∀ address, address < layout.nodeMarkerBase → final.heap[address]? = state.heap[address]?) := by
  obtain ⟨final, ticks, peak, trace, time, space, channelLedger, unique, size, frame,
      stack, output, count, cursorFinal, depth, zero, one, pc, live⟩ :=
    scope_loop_execution program layout loop publish resume done code stored.channelDimension
      storageFits labels state channels cursor position running stored.allocation
      stored.channelsUnique stored.channelLedger stored.zero stored.one countHeld cursorHeld scopeEnd scope
  refine ⟨final, ticks, peak, trace, time, space, ?_, stack, output, count, cursorFinal, pc, live, ?_⟩
  · refine ⟨?_, stored.nodeDimension, stored.channelDimension, size.trans stored.allocation,
      ?_, channelLedger, unique, ?_, ?_, depth.trans stored.depth,
      zero.trans stored.zero, one.trans stored.one⟩
    · intro address
      rw [frame address.val (Or.inl (by have := address.isLt; omega))]
      exact stored.sourceRetained address
    · refine ⟨?_, ?_, ?_⟩
      · rw [frame layout.nodeCountSlot (Or.inr (Or.inr rfl))]
        exact stored.completed.count
      · intro rank
        rw [frame (layout.nodeLedgerBase + rank.val) (Or.inr (Or.inl (by
          have capacity := logical.completedUnique.length_le_card
          simp only [Fintype.card_fin] at capacity
          have := rank.isLt
          simp only [SharedLayout.mapBase, SharedLayout.nodeLedgerBase, SharedLayout.channelLedgerBase]
          rw [stored.nodeDimension]
          omega)))]
        exact stored.completed.ledger rank
      · intro rank
        rw [frame (layout.mapBase + (logical.completed[rank]).val) (Or.inr (Or.inl (by
          have bound := (logical.completed[rank]).isLt
          simp only [SharedLayout.mapBase, SharedLayout.channelLedgerBase]
          rw [stored.nodeDimension]
          omega)))]
        exact stored.completed.map rank
    · intro node
      rw [frame (layout.nodeMarkerBase + node.val) (Or.inl (by
        have := node.isLt
        simp only [SharedLayout.channelMarkerBase]
        rw [stored.nodeDimension]
        omega))]
      exact stored.flags node
    · intro node member channel scopeMember
      exact (publishLabels_mem channels labels channel).mpr
        (Or.inl (stored.completedScope node member channel scopeMember))
  · intro address beforeMarker
    apply frame address
    exact Or.inl (by simp only [SharedLayout.channelMarkerBase]; omega)



/-- The physical loop follows an original row suffix. Its only recursive node
argument is the strictly smaller-ID induction hypothesis of the containing
node-body theorem. Every tail state is the endpoint of the preceding trace. -/
private noncomputable def child_slice_execution
    (program : Program width 8) (graph : DAG n) (layout : SharedLayout)
    (caller : Array (Word width)) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (base : Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (code : ChildCodeAt program layout base (caller.size + 4 * rows.length)
      (caller.size + 2 * rows.length))
    (storageFits : layout.storageEnd < 2 ^ width)
    (current : Fin graph.nodeCount)
    (bodyIH : ∀ (child : Fin graph.nodeCount), child.val < current.val →
      ∀ (state : State width 8) (logical : DFSState graph) (channels : List (Channel n))
        (ancestors : List (Fin graph.nodeCount)),
      TraversalStored graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
        state logical channels →
      logical.active = child :: ancestors → AncestorsAbove graph child ancestors →
      state.pc = word width (base + 28) → state.halted = false →
      state.reg 4 = word width (graph.node child).children.length →
      state.reg 6 = word width (caller.size + 6 * rows.length +
        (ForestIndexedOperands.rowChildren (rows.take child.val)).length) →
      (∃ tail, state.stack = word width child.val :: tail) →
      NodeBodyTrace program graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
        base child state logical channels)
    (originalCursor cursor : Nat) (remaining : List (Fin current.val))
    (suffix : OriginalChildSuffix graph current originalCursor cursor remaining)
    (state : State width 8) (logical : DFSState graph) (channels : List (Channel n))
    (ancestors : List (Fin graph.nodeCount))
    (stored : TraversalStored graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
      state logical channels)
    (active : logical.active = current :: ancestors)
    (above : AncestorsAbove graph current ancestors)
    (depthFits : logical.active.length + 1 < 2 ^ width)
    (position : state.pc = word width (base + 28)) (running : state.halted = false)
    (count : state.reg 4 = word width remaining.length)
    (cursorHeld : state.reg 6 = word width cursor)
    (endBound : cursor + remaining.length ≤ layout.nodeMarkerBase)
    (scope : ScopeStored state.heap cursor remaining) :
    ChildSliceTrace program graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
      base current remaining cursor state logical channels := by
  cases remaining with
  | nil =>
      exact child_slice_empty program graph layout _ base _ _ code current state logical channels
        cursor stored position running count cursorHeld
  | cons child rest =>
      have markerBelow : layout.nodeMarkerBase < layout.storageEnd := by
        simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot,
          SharedLayout.nodeLedgerBase]
        omega
      have cursorFits : cursor + 1 < 2 ^ width := by
        simp only [List.length_cons] at endBound
        omega
      have countFits : rest.length + 1 < 2 ^ width := by
        simp only [List.length_cons] at endBound
        omega
      have sourceBound : cursor < state.heap.size := by
        rw [stored.allocation]
        simp only [List.length_cons] at endBound
        omega
      have sourceCell : state.heap[cursor]'sourceBound =
          word width (graph.childIndex current child).val := by
        have cell := scope ⟨0, by simp only [List.length_cons]; omega⟩
        simp only [Nat.add_zero, Fin.getElem_fin, List.getElem_cons_zero] at cell
        rw [Array.getElem?_eq_getElem sourceBound] at cell
        exact Option.some.inj cell
      have original := original_child_suffix_member graph current originalCursor cursor child rest suffix
      have tailSuffix := original_child_suffix_tail graph current originalCursor cursor child rest suffix
      by_cases seen : graph.childIndex current child ∈ logical.completed
      · let next := Classical.choose (child_stale_test program graph layout _ base _ _ code
          state logical channels (graph.childIndex current child) cursor rest.length stored seen
          storageFits position running cursorFits countFits cursorHeld count sourceBound sourceCell)
        have endpoint := Classical.choose_spec (child_stale_test program graph layout _ base _ _ code
          state logical channels (graph.childIndex current child) cursor rest.length stored seen
          storageFits position running cursorFits countFits cursorHeld count sourceBound sourceCell)
        rcases endpoint with ⟨trace, nextStored, nextCount, nextCursor, nextZero, nextOne,
          nextDepth, nextHeap, nextStack, nextOutput, nextPosition, nextRunning⟩
        have tailScope : ScopeStored next.heap (cursor + 1) rest := by
          rw [nextHeap]
          exact scope_tail state.heap cursor child rest scope
        let tailTrace := child_slice_execution program graph layout caller rows roots base matched
          sourceSize code storageFits current bodyIH originalCursor (cursor + 1) rest tailSuffix
          next logical channels ancestors nextStored active above depthFits nextPosition nextRunning
          nextCount nextCursor (by simp only [List.length_cons] at endBound; omega) tailScope
        exact child_slice_stale_cons program graph layout _ base current child rest cursor state next
          logical channels seen stored trace nextHeap nextStack nextOutput nextDepth nextZero nextOne tailTrace
      · let tested : State width 8 := state.advance
        have testTrace : Execution program state tested 1 state.liveWords := by
          simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, tested] using
            streamTest_execution program state (base + 28) (base + 47) (rest.length + 1)
              code.test position running (by have := code.fits; omega) countFits count
        have testedStored : TraversalStored graph layout
            (ForestIndexedOperands.cacheHeap width caller rows roots) tested logical channels :=
          traversal_readonly graph layout _ state tested logical channels stored rfl rfl rfl rfl
        have testedPosition : tested.pc = word width (base + 29) := by
          have entryFits : base + 28 < 2 ^ width := by have := code.fits; omega
          have entryVal : (word width (base + 28)).val = base + 28 := Nat.mod_eq_of_lt entryFits
          change word width (state.pc.val + 1) = word width (base + 29)
          rw [position, entryVal]
        let metadata := retained_child_metadata caller tested.heap graph rows roots layout matched
          stored.sourceRetained sourceSize stored.allocation (graph.childIndex current child)
        have recurse := child_fresh_recursive program graph layout _ base _ _ code current child
          tested logical channels cursor rest.length ancestors active above seen metadata sourceSize
          testedStored storageFits depthFits testedPosition running cursorFits countFits cursorHeld count
          sourceBound sourceCell
          (fun entered inactive enterStored enterPosition enterRunning enterCount enterCursor enterStack =>
            bodyIH (graph.childIndex current child) (graph.childIndex_lt current child)
              entered (activateChild graph logical (graph.childIndex current child) seen inactive)
              channels (current :: ancestors) enterStored (by simpa only [activateChild, active])
              (child_ancestors_above graph current child ancestors above) enterPosition enterRunning
              enterCount enterCursor ⟨_, enterStack⟩)
        let entered := Classical.choose recurse
        let inactive := Classical.choose (Classical.choose_spec recurse)
        let body := Classical.choose (Classical.choose_spec (Classical.choose_spec recurse))
        let returned := Classical.choose (Classical.choose_spec
          (Classical.choose_spec (Classical.choose_spec recurse)))
        let shape := Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec (Classical.choose_spec recurse))))
        have endpoint := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec (Classical.choose_spec recurse))))
        change entered.liveWords = tested.liveWords + 3 ∧
          Execution program tested returned (20 + body.ticks + 24)
            (max (tested.liveWords + 3) body.peak) ∧
          TraversalStored graph layout _ returned
            (completeLogical graph body.logical (graph.childIndex current child) logical.active
              shape body.childDone) body.channels ∧
          (∀ address, address < layout.nodeMarkerBase → returned.heap[address]? = tested.heap[address]?) ∧
          returned.stack = tested.stack ∧ returned.output = tested.output ∧
          returned.reg 4 = word width rest.length ∧ returned.reg 6 = word width (cursor + 1) ∧
          returned.pc = word width (base + 28) ∧ returned.halted = false at endpoint
        rcases endpoint with ⟨enteredLive, recursiveTrace, returnedStored, returnedValues, returnedStack,
          returnedOutput, returnedCount, returnedCursor, returnedPosition, returnedRunning⟩
        have first : Execution program state returned (45 + body.ticks)
            (max (state.liveWords + 3) body.peak) := by
          have joined : Execution program state returned (1 + (20 + body.ticks + 24))
              (max state.liveWords (max (tested.liveWords + 3) body.peak)) :=
            testTrace.append recursiveTrace
          have ticksEqual : 1 + (20 + body.ticks + 24) = 45 + body.ticks := by omega
          have testedLive : tested.liveWords = state.liveWords := rfl
          have peakEqual : max state.liveWords (max (tested.liveWords + 3) body.peak) =
              max (state.liveWords + 3) body.peak := by omega
          have tickTrace := Eq.mp (congrArg (fun ticks => Execution program state returned ticks
            (max state.liveWords (max (tested.liveWords + 3) body.peak))) ticksEqual) joined
          exact Eq.mp (congrArg (fun peak => Execution program state returned (45 + body.ticks) peak)
            peakEqual) tickTrace
        have returnedLive : returned.liveWords = state.liveWords := by
          have stackEqual : returned.stack = state.stack := returnedStack
          have outputEqual : returned.output = state.output := returnedOutput
          simp only [State.liveWords, returnedStored.allocation, stored.allocation,
            stackEqual, outputEqual]
        have firstSpace : max (state.liveWords + 3) body.peak ≤ state.liveWords + 3 * current.val + 3 := by
          have bodySpace := body.space
          have lower := graph.childIndex_lt current child
          have bodyBound : body.peak ≤ entered.liveWords + 3 * (graph.childIndex current child).val + 3 := bodySpace
          have entrySize : entered.liveWords = state.liveWords + 3 := enteredLive
          exact max_le (by omega) (by omega)
        have tailScope : ScopeStored returned.heap (cursor + 1) rest := by
          intro index
          have beforeMarker : cursor + 1 + index.val < layout.nodeMarkerBase := by
            have := index.isLt
            simp only [List.length_cons] at endBound
            omega
          rw [returnedValues _ beforeMarker]
          exact scope_tail state.heap cursor child rest scope index
        let middle := completeLogical graph body.logical (graph.childIndex current child)
          logical.active shape body.childDone
        let tailTrace := child_slice_execution program graph layout caller rows roots base matched
          sourceSize code storageFits current bodyIH originalCursor (cursor + 1) rest tailSuffix
          returned middle body.channels ancestors returnedStored active above depthFits
          returnedPosition returnedRunning returnedCount returnedCursor
          (by simp only [List.length_cons] at endBound; omega) tailScope
        exact child_slice_fresh_cons program graph layout _ base current child rest cursor state entered
          returned logical channels stored seen inactive original body shape
          (show entered.liveWords = state.liveWords + 3 from enteredLive) first firstSpace
          returnedValues returnedStack returnedOutput
          (returnedStored.allocation.trans stored.allocation.symm) tailTrace
termination_by structural remaining


/-- The body endpoint composes the original child traversal, fetched scope
preparation and the original direct-channel stream. Logical fields follow the
source DAG identity; all machine fields follow the same composed trace. -/
private def body_from_children (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width)) (base : Nat)
    (current : Fin graph.nodeCount) (initial : State width 8) (before : DFSState graph)
    (initialChannels : List (Channel n)) (cursor : Nat)
    (children : ChildSliceTrace program graph layout source base current
      (graph.node current).children cursor initial before initialChannels)
    (prepared final : State width 8) (prepareTicks scopeTicks scopePeak : Nat)
    (prepareTrace : Execution program children.final prepared prepareTicks children.final.liveWords)
    (prepareTime : prepareTicks ≤ 16)
    (prepareHeap : prepared.heap = children.final.heap)
    (prepareStack : prepared.stack = children.final.stack)
    (prepareOutput : prepared.output = children.final.output)
    (scopeTrace : Execution program prepared final scopeTicks scopePeak)
    (scopeTime : scopeTicks ≤ 27 * (graph.node current).directChannels.length + 1)
    (scopeSpace : scopePeak ≤ prepared.liveWords + 3)
    (stored : TraversalStored graph layout source final children.logical
      (publishLabels children.channels (graph.node current).directChannels))
    (scopeValues : ∀ address, address < layout.nodeMarkerBase →
      final.heap[address]? = prepared.heap[address]?)
    (scopeStack : final.stack = prepared.stack) (scopeOutput : final.output = prepared.output)
    (count : final.reg 4 = word width 0)
    (position : final.pc = word width (base + 96)) (running : final.halted = false)
    (initialStored : TraversalStored graph layout source initial before initialChannels) :
    NodeBodyTrace program graph layout source base current initial before initialChannels := by
  have childLive : children.final.liveWords = initial.liveWords := by
    simp only [State.liveWords, children.stored.allocation, initialStored.allocation,
      children.stack, children.output]
  have preparedLive : prepared.liveWords = initial.liveWords := by
    simp only [State.liveWords, prepareHeap, prepareStack, prepareOutput,
      children.stored.allocation, initialStored.allocation, children.stack, children.output]
  refine {
    final := final, logical := children.logical,
    channels := publishLabels children.channels (graph.node current).directChannels,
    ticks := children.ticks + prepareTicks + scopeTicks,
    peak := max (max children.peak children.final.liveWords) scopePeak,
    execution := (children.execution.append prepareTrace).append scopeTrace,
    charged := ?_, space := ?_,
    deltaSpace := by
      have childBound := children.deltaSpace
      have scopeBound := scopeSpace
      rw [preparedLive] at scopeBound
      rw [childLive]
      exact max_le (max_le childBound (by omega)) (by omega), stored := stored, active := children.active,
    completed := children.completed, addedPrefix := children.addedPrefix,
    childDone := children.childDone, ownScope := ?_, inside := children.inside,
    channelsExact := ?_, postorder := children.postorder, values := ?_,
    stack := scopeStack.trans (prepareStack.trans children.stack),
    output := scopeOutput.trans (prepareOutput.trans children.output), count := count,
    depth := ?_, zero := stored.zero.trans initialStored.zero.symm,
    one := stored.one.trans initialStored.one.symm, position := position, running := running }
  · have charge := children.charged
    omega
  · have childSpace := children.space
    rw [preparedLive] at scopeSpace
    rw [childLive]
    exact max_le (max_le childSpace (by omega)) (by omega)
  · intro channel included
    exact (publishLabels_mem children.channels (graph.node current).directChannels channel).mpr
      (Or.inr included)
  · intro channel
    rw [publishLabels_mem, children.channelsExact, graph.scope_eq]
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_biUnion]
    constructor
    · intro covered
      rcases covered with (old | descendant) | direct
      · exact Or.inl old
      · rcases descendant with ⟨child, member, supported⟩
        exact Or.inr (Or.inr ⟨child, member, supported⟩)
      · exact Or.inr (Or.inl direct)
    · intro covered
      rcases covered with old | (direct | descendant)
      · exact Or.inl (Or.inl old)
      · exact Or.inr direct
      · exact Or.inl (Or.inr descendant)
  · intro address below
    exact (scopeValues address below).trans
      ((by rw [prepareHeap] : prepared.heap[address]? = children.final.heap[address]?).trans
        (children.values address below))
  · rw [stored.depth, children.active]
    exact initialStored.depth.symm


/-- Uniform node-body execution follows the original source children in their
stored order and then its original direct channel occurrences. The smaller-ID
induction is discharged here rather than supplied to the public endpoint. -/
private theorem whole_node_body
    (program : Program width 8) (graph : DAG n) (layout : SharedLayout)
    (caller : Array (Word width)) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (base : Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (physical : ∀ phase : Fin 120, program[base + phase.val]? =
      (dfsFromCache width caller rows roots base layout)[phase.val]?)
    (codeFits : base + 120 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (current : Fin graph.nodeCount) :
    ∀ (initial : State width 8) (before : DFSState graph) (channels : List (Channel n))
      (ancestors : List (Fin graph.nodeCount)),
    TraversalStored graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
      initial before channels →
    before.active = current :: ancestors → AncestorsAbove graph current ancestors →
    initial.pc = word width (base + 28) → initial.halted = false →
    initial.reg 4 = word width (graph.node current).children.length →
    initial.reg 6 = word width (caller.size + 6 * rows.length +
      (ForestIndexedOperands.rowChildren (rows.take current.val)).length) →
    (∃ suffix, initial.stack = word width current.val :: suffix) →
    Nonempty (NodeBodyTrace program graph layout
      (ForestIndexedOperands.cacheHeap width caller rows roots) base current initial before channels) := by
  classical
  refine Fin.strong_induction_on (fun current smaller => ?_) current
  intro initial before channels ancestors stored active above position running
    count cursorHeld stackHeld
  let childCode := fixed_child_code program caller rows roots base layout physical codeFits
  let scopeCode := fixed_scope_code program caller rows roots base layout physical codeFits
  let prepCode := fixed_scope_preparation program caller rows roots base layout physical codeFits
  let childMetadata := retained_child_metadata caller initial.heap graph rows roots layout matched
    stored.sourceRetained sourceSize stored.allocation current
  let originalCursor := caller.size + 6 * rows.length +
    (ForestIndexedOperands.rowChildren (rows.take current.val)).length
  let children := child_slice_execution program graph layout caller rows roots base matched
    sourceSize childCode storageFits current
    (fun child lower state logical labels parents childStored childActive childAbove childPosition
      childRunning childCount childCursor childStack =>
      Classical.choice (smaller child lower state logical labels parents childStored childActive
        childAbove childPosition childRunning childCount childCursor childStack))
    originalCursor originalCursor (graph.node current).children
    ⟨[], by simp, by simp⟩ initial before channels ancestors stored active above
    (active_depth_fits graph layout _ initial before channels stored storageFits)
    position running count cursorHeld childMetadata.endBound childMetadata.slice
  let metadata := retained_scope_metadata caller children.final.heap graph rows roots layout matched
    children.stored.sourceRetained sourceSize children.stored.allocation current
  have originalValid : current.val < rows.length := by rw [matched.length_eq]; exact current.isLt
  have sourceBelowMarker : layout.sourceEnd ≤ layout.nodeMarkerBase := by
    simp only [SharedLayout.nodeMarkerBase]
    omega
  have tagAddress : caller.size + 2 * current.val < layout.sourceEnd := by
    rw [← sourceSize, ForestIndexedOperands.cacheHeap_size]
    omega
  have headAddress : caller.size + 1 + 2 * current.val + 1 ≤ layout.nodeMarkerBase := by
    have sourceLength := sourceSize
    simp only [ForestIndexedOperands.cacheHeap_size] at sourceLength
    omega
  have arityAddress : caller.size + 4 * rows.length + 1 + 2 * current.val < layout.storageEnd := by
    have sourceLength := sourceSize
    simp only [ForestIndexedOperands.cacheHeap_size] at sourceLength
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have directoryAddress : caller.size + 2 * rows.length + 1 + 2 * current.val < layout.storageEnd := by
    have sourceLength := sourceSize
    simp only [ForestIndexedOperands.cacheHeap_size] at sourceLength
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have tagFits : ForestIndexedOperands.tagValue graph current < 2 ^ width := by
    cases gateEq : graph.node current <;> simp only [ForestIndexedOperands.tagValue, gateEq] <;> omega
  let suffix := Classical.choose stackHeld
  have initialStack := Classical.choose_spec stackHeld
  have childStack : children.final.stack = word width current.val :: suffix :=
    children.stack.trans initialStack
  obtain ⟨prepared, prepareTicks, prepareTrace, prepareTime, prepareHeap, prepareStack,
    prepareOutput, prepareCount, prepareCursor, prepareRegs, preparePosition, prepareRunning⟩ :=
    scope_prepare_execution program children.final base caller.size (caller.size + 1)
      (caller.size + 4 * rows.length + 1) (caller.size + 2 * rows.length + 1)
      current.val (ForestIndexedOperands.tagValue graph current) (graph.node current).guardLabels.length
      (caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
        (ForestIndexedOperands.rowGuards (rows.take current.val)).length) suffix prepCode
      children.position children.running children.stored.zero childStack
      (by have := current.isLt; have := children.stored.nodeDimension;
          simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot, SharedLayout.nodeMarkerBase] at storageFits; omega)
      tagFits (by omega) (by omega) (by omega) (by omega)
      metadata.tagBound (by simpa only [Nat.add_assoc, Nat.add_comm 1] using metadata.arityBound)
      (by simpa only [Nat.add_assoc, Nat.add_comm 1] using metadata.directoryBound)
      metadata.tagCell (by simpa only [Nat.add_assoc, Nat.add_comm 1] using metadata.arityCell)
      (by simpa only [Nat.add_assoc, Nat.add_comm 1] using metadata.directoryCell)
  let scopeCursor := if ForestIndexedOperands.tagValue graph current = 1 then
    caller.size + 1 + 2 * current.val else
    caller.size + 6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
      (ForestIndexedOperands.rowGuards (rows.take current.val)).length
  have prepareStored : TraversalStored graph layout _ prepared children.logical children.channels :=
    traversal_readonly graph layout _ children.final prepared children.logical children.channels
      children.stored prepareHeap (prepareRegs 7 (by decide) (by decide) (by decide) (by decide) (by decide))
      (prepareRegs 2 (by decide) (by decide) (by decide) (by decide) (by decide))
      (prepareRegs 3 (by decide) (by decide) (by decide) (by decide) (by decide))
  have originalCount : prepared.reg 4 = word width (graph.node current).directChannels.length := by
    cases gateEq : graph.node current <;>
      simpa only [ForestIndexedOperands.tagValue, gateEq, Gate.directChannels, Gate.guardLabels,
        List.length_nil, List.length_singleton, ite_true, ite_false, Nat.reduceEqDiff] using prepareCount
  have originalScope : ScopeStored prepared.heap scopeCursor (graph.node current).directChannels := by
    rw [prepareHeap]
    suffices selected : ∀ gate : Gate n current.val, graph.node current = gate →
        ScopeStored children.final.heap scopeCursor gate.directChannels from selected _ rfl
    intro gate gateEq
    cases gate with
    | input channel =>
        simpa only [scopeCursor, ForestIndexedOperands.tagValue, gateEq, Gate.directChannels,
          ite_true, Nat.add_assoc, Nat.add_comm 1 (2 * current.val)] using
          input_scope_stored caller children.final.heap graph rows roots matched
            children.stored.sourceRetained current channel gateEq
    | zero => simp [scopeCursor, ForestIndexedOperands.tagValue, gateEq, Gate.directChannels, ScopeStored]
    | disj references => simp [scopeCursor, ForestIndexedOperands.tagValue, gateEq, Gate.directChannels, ScopeStored]
    | guard child labels => simpa only [scopeCursor, ForestIndexedOperands.tagValue, gateEq,
        Gate.directChannels, Gate.guardLabels, ite_false, Nat.reduceEqDiff] using metadata.scope
    | liveAnd left right => simp [scopeCursor, ForestIndexedOperands.tagValue, gateEq, Gate.directChannels, ScopeStored]
  have scopeEnd : scopeCursor + (graph.node current).directChannels.length ≤ layout.channelMarkerBase := by
    have guardEnd := metadata.guardEnd
    cases gateEq : graph.node current <;>
      simp only [scopeCursor, ForestIndexedOperands.tagValue, gateEq, Gate.directChannels,
        Gate.guardLabels, List.length_nil, List.length_singleton, ite_true, ite_false,
        Nat.reduceEqDiff, SharedLayout.channelMarkerBase] at * <;> omega
  obtain ⟨final, scopeTicks, scopePeak, scopeTrace, scopeTime, scopeSpace, finalStored,
    scopeStack, scopeOutput, finalCount, finalCursor, finalPosition, finalRunning, scopeValues⟩ :=
    scope_loop_framed program graph layout _ children.logical prepared children.channels
      (graph.node current).directChannels (base + 67) (base + 80) (base + 90) (base + 96)
      scopeCursor scopeCode storageFits
      (by rw [sourceSize]; simp only [SharedLayout.channelMarkerBase, SharedLayout.nodeMarkerBase]; omega)
      prepareStored preparePosition prepareRunning originalCount prepareCursor scopeEnd originalScope
  exact ⟨body_from_children program graph layout _ base current initial before channels originalCursor
    children prepared final prepareTicks scopeTicks scopePeak prepareTrace prepareTime prepareHeap
    prepareStack prepareOutput scopeTrace scopeTime scopeSpace finalStored scopeValues scopeStack
    scopeOutput finalCount finalPosition finalRunning stored⟩


/-- The fixed fetched DFS body consumes every original child occurrence and
publishes every original direct channel, deriving fresh recursive executions
by strictly smaller source IDs. Completion and caller return begin at offset
96 after this endpoint. -/
theorem node_body_execution
    (program : Program width 8) (graph : DAG n) (layout : SharedLayout)
    (caller : Array (Word width)) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (base : Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (physical : ∀ phase : Fin 120, program[base + phase.val]? =
      (dfsFromCache width caller rows roots base layout)[phase.val]?)
    (codeFits : base + 120 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (current : Fin graph.nodeCount) (initial : State width 8) (before : DFSState graph)
    (channels : List (Channel n)) (ancestors : List (Fin graph.nodeCount))
    (stored : TraversalStored graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
      initial before channels)
    (active : before.active = current :: ancestors) (above : AncestorsAbove graph current ancestors)
    (position : initial.pc = word width (base + 28)) (running : initial.halted = false)
    (count : initial.reg 4 = word width (graph.node current).children.length)
    (cursor : initial.reg 6 = word width (caller.size + 6 * rows.length +
      (ForestIndexedOperands.rowChildren (rows.take current.val)).length))
    (stack : ∃ suffix, initial.stack = word width current.val :: suffix) :
    ∃ (final : State width 8) (after : DFSState graph) (labels : List (Channel n)) (ticks peak : Nat),
      Execution program initial final ticks peak ∧
      ticks + 46 * freshWeight graph before.completed ≤
        46 * freshWeight graph after.completed + 17 * (graph.node current).children.length +
          27 * (graph.node current).directChannels.length + 18 ∧
      peak ≤ initial.liveWords + 3 * current.val + 3 ∧
      peak ≤ initial.liveWords + 3 * (after.completed.length - before.completed.length) + 3 ∧
      TraversalStored graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
        final after labels ∧ after.active = before.active ∧
      after.completed = (graph.node current).children.foldl
        (fun completed child => discoverNode graph (graph.childIndex current child) completed) before.completed ∧
      (∃ added, after.completed = before.completed ++ added) ∧
      (∀ child ∈ (graph.node current).children, graph.childIndex current child ∈ after.completed) ∧
      (∀ channel ∈ (graph.node current).directChannels, channel ∈ labels) ∧
      (∀ node ∈ after.completed, node ∈ before.completed ∨ node ∈ graph.cone current) ∧
      (∀ channel, channel ∈ labels ↔ channel ∈ channels ∨ channel ∈ graph.scope current) ∧
      (Postorder graph before.completed → Postorder graph after.completed) ∧
      (∀ address, address < layout.nodeMarkerBase → final.heap[address]? = initial.heap[address]?) ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 4 = word width 0 ∧ final.reg 7 = initial.reg 7 ∧
      final.reg 2 = initial.reg 2 ∧ final.reg 3 = initial.reg 3 ∧
      final.pc = word width (base + 96) ∧ final.halted = false := by
  obtain ⟨body⟩ := whole_node_body program graph layout caller rows roots base matched sourceSize
    physical codeFits storageFits current initial before channels ancestors stored active above
    position running count cursor stack
  exact ⟨body.final, body.logical, body.channels, body.ticks, body.peak, body.execution,
    body.charged, body.space, body.deltaSpace, body.stored, body.active, body.completed, body.addedPrefix,
    body.childDone, body.ownScope, body.inside, body.channelsExact, body.postorder, body.values,
    body.stack, body.output, body.count, body.depth, body.zero, body.one, body.position, body.running⟩

private theorem complete_root_resume (program : Program width 8) (state : State width 8)
    (entry returnEntry resume loop rootNext countSlot mapBase ledgerBase identifier rank cursor remaining : Nat)
    (suffix : List (Word width))
    (finishAt : ∀ phase : Fin 13, program[entry + phase.val]? =
      (finishLedgerCode width countSlot mapBase ledgerBase)[phase.val]?)
    (returnAt : ∀ phase : Fin 5, program[returnEntry + phase.val]? =
      (finishReturnCode width resume rootNext)[phase.val]?)
    (resumeAt : ∀ phase : Fin 6, program[rootNext + phase.val]? = (resumeCode width loop)[phase.val]?)
    (joined : returnEntry = entry + 13)
    (position : state.pc = word width entry) (running : state.halted = false)
    (finishFits : entry + 13 < 2 ^ width) (returnFits : returnEntry + 5 < 2 ^ width)
    (resumeFits : rootNext + 6 < 2 ^ width) (loopFits : loop < 2 ^ width)
    (stack : state.stack = word width identifier :: word width cursor :: word width (remaining + 1) :: suffix)
    (one : state.reg 3 = word width 1) (zero : state.reg 2 = word width 0)
    (depthHeld : state.reg 7 = word width 1)
    (depthFits : 1 < 2 ^ width)
    (cursorFits : cursor + 1 < 2 ^ width) (remainingFits : remaining + 1 < 2 ^ width)
    (countFits : countSlot < 2 ^ width) (mapFits : mapBase + identifier < 2 ^ width)
    (ledgerFits : ledgerBase + rank < 2 ^ width) (rankFits : rank + 1 < 2 ^ width)
    (countBound : countSlot < state.heap.size)
    (mapBound : mapBase + identifier < state.heap.size)
    (ledgerBound : ledgerBase + rank < state.heap.size)
    (countCell : state.heap[countSlot]'countBound = word width rank) :
    ∃ final, Execution program state final 23 state.liveWords ∧
      final.heap = ((state.heap.set (mapBase + identifier) (word width rank) mapBound).set
        (ledgerBase + rank) (word width identifier) (by simpa using ledgerBound)).set
          countSlot (word width (rank + 1)) (by simpa using countBound) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.reg 7 = word width 0 ∧ final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧
      final.pc = word width loop ∧ final.halted = false := by
  obtain ⟨completed, first, completedHeap, completedStack, completedOutput,
      completedId, completedRank, completedRegs, completedPC, completedRunning⟩ :=
    finishLedger_execution program state entry countSlot mapBase ledgerBase identifier rank
      (word width cursor :: word width (remaining + 1) :: suffix) finishAt position running
      finishFits stack one countFits mapFits ledgerFits rankFits countBound mapBound ledgerBound countCell
  have completedZero : completed.reg 2 = state.reg 2 := completedRegs 2 (by decide) (by decide) (by decide)
  have completedOne : completed.reg 3 = state.reg 3 := completedRegs 3 (by decide) (by decide) (by decide)
  have completedDepth : completed.reg 7 = state.reg 7 := completedRegs 7 (by decide) (by decide) (by decide)
  obtain ⟨returned, second, returnedHeap, returnedStack, returnedOutput, returnedDepth,
      returnedRegs, returnedPC, returnedRunning⟩ :=
    finishReturn_root program completed returnEntry resume rootNext identifier
      (word width cursor :: word width (remaining + 1) :: suffix) returnAt
      (by simpa only [joined] using completedPC) completedRunning returnFits
      (completedStack.trans stack) (completedDepth.trans depthHeld) depthFits
      (completedZero.trans zero)
  have returnedZero : returned.reg 2 = state.reg 2 :=
    (returnedRegs 2 (by decide) (by decide) (by decide)).trans completedZero
  have returnedOne : returned.reg 3 = state.reg 3 :=
    (returnedRegs 3 (by decide) (by decide) (by decide)).trans completedOne
  obtain ⟨final, third, finalCount, finalCursor, finalId, finalZero, finalOne, finalDepth,
      finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    resume_execution program returned rootNext loop cursor remaining suffix resumeAt returnedPC returnedRunning
      resumeFits loopFits returnedStack (returnedZero.trans zero) (returnedOne.trans one)
      cursorFits remainingFits
  have completedLive : completed.liveWords = state.liveWords := by
    simp only [State.liveWords, completedHeap, Array.size_set, completedStack, completedOutput]
  have returnedLive : returned.liveWords ≤ state.liveWords := by
    simp only [State.liveWords, returnedHeap, completedHeap, Array.size_set,
      returnedStack, returnedOutput, completedOutput, stack, List.length_cons]
    omega
  refine ⟨final, ?_, finalHeap.trans (returnedHeap.trans completedHeap), finalStack,
    finalOutput.trans (returnedOutput.trans completedOutput), finalCount, finalCursor,
    finalDepth.trans returnedDepth, finalZero.trans returnedZero, finalOne.trans returnedOne,
    finalPC, finalRunning⟩
  have trace := (first.append second).append third
  simpa only [completedLive, Nat.max_self, Nat.max_eq_left returnedLive] using trace


private theorem complete_root_global (program : Program width 8) (graph : DAG n)
    (layout : SharedLayout) (source : Array (Word width))
    (logical : DFSState graph) (state : State width 8) (channels : List (Channel n))
    (node : Fin graph.nodeCount)
    (entry resume loop rootNext cursor remaining : Nat) (suffix : List (Word width))
    (finishAt : ∀ phase : Fin 13, program[entry + phase.val]? =
      (finishLedgerCode width layout.nodeCountSlot layout.mapBase layout.nodeLedgerBase)[phase.val]?)
    (returnAt : ∀ phase : Fin 5, program[entry + 13 + phase.val]? =
      (finishReturnCode width resume rootNext)[phase.val]?)
    (resumeAt : ∀ phase : Fin 6, program[rootNext + phase.val]? = (resumeCode width loop)[phase.val]?)
    (sourceSize : source.size = layout.sourceEnd)
    (stored : TraversalStored graph layout source state logical channels)
    (activeShape : logical.active = node :: [])
    (childrenDone : ∀ child ∈ (graph.node node).children,
      graph.childIndex node child ∈ logical.completed)
    (scopeDone : ∀ channel ∈ (graph.node node).directChannels, channel ∈ channels)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 18 < 2 ^ width) (resumeFits : rootNext + 6 < 2 ^ width)
    (loopFits : loop < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (depthFits : 1 < 2 ^ width)
    (cursorFits : cursor + 1 < 2 ^ width) (remainingFits : remaining + 1 < 2 ^ width)
    (stack : state.stack = word width node.val :: word width cursor ::
      word width (remaining + 1) :: suffix) :
    ∃ final, Execution program state final 23 state.liveWords ∧
      TraversalStored graph layout source final
        (completeLogical graph logical node [] activeShape childrenDone) channels ∧
      (∀ address, address < layout.nodeMarkerBase → final.heap[address]? = state.heap[address]?) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.reg 4 = word width remaining ∧ final.reg 6 = word width (cursor + 1) ∧
      final.pc = word width loop ∧ final.halted = false := by
  have fresh : node ∉ logical.completed :=
    (List.disjoint_cons_right.mp (activeShape ▸ logical.separate)).1
  have nodeRoom : node.val < layout.nodeCount := by rw [stored.nodeDimension]; exact node.isLt
  have rankRoom : logical.completed.length < layout.nodeCount := by
    rw [stored.nodeDimension]
    exact completed_capacity graph logical.completed logical.completedUnique node fresh
  have heapFits : state.heap.size < 2 ^ width := by
    rw [stored.allocation]
    exact storageFits
  have nodeCountFits : layout.nodeCount < 2 ^ width := by
    have below : layout.nodeCount < layout.storageEnd := by
      simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
      omega
    omega
  have mapBound : layout.mapBase + node.val < state.heap.size := by
    rw [stored.allocation]
    simp only [SharedLayout.mapBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have ledgerBound : layout.nodeLedgerBase + logical.completed.length < state.heap.size := by
    rw [stored.allocation]
    simp only [SharedLayout.nodeLedgerBase, SharedLayout.storageEnd, SharedLayout.nodeCountSlot]
    omega
  have countBound : layout.nodeCountSlot < state.heap.size := by
    rw [stored.allocation]
    simp only [SharedLayout.storageEnd]
    omega
  have countCell : state.heap[layout.nodeCountSlot]'countBound = word width logical.completed.length := by
    have cell := stored.completed.count
    rw [Array.getElem?_eq_getElem countBound] at cell
    exact Option.some.inj cell
  obtain ⟨final, trace, heap, caller, output, count, cursorFinal, depth, zero, one, pc, live⟩ :=
    complete_root_resume program state entry (entry + 13) resume loop rootNext
      layout.nodeCountSlot layout.mapBase layout.nodeLedgerBase node.val logical.completed.length
      cursor remaining suffix finishAt returnAt resumeAt rfl position running
      (by omega) (by omega) resumeFits loopFits stack stored.one stored.zero
      (by simpa only [activeShape, List.length_cons, List.length_nil, Nat.zero_add] using stored.depth) depthFits
      cursorFits remainingFits (by omega) (by omega) (by omega) (by omega)
      countBound mapBound ledgerBound countCell
  refine ⟨final, trace, ?_, ?_, caller, output, count, cursorFinal, pc, live⟩
  refine ⟨?_, stored.nodeDimension, stored.channelDimension, ?_, ?_, ?_,
    stored.channelsUnique, ?_, ?_, depth, zero.trans stored.zero, one.trans stored.one⟩
  · rw [heap]
    exact completion_cache_frame state.heap source layout node.val logical.completed.length
      stored.sourceRetained sourceSize mapBound ledgerBound countBound
  · simp only [heap, Array.size_set, stored.allocation]
  · rw [heap]
    exact completion_stored graph layout state.heap logical.completed node stored.nodeDimension
      logical.completedUnique fresh stored.completed mapBound ledgerBound countBound
  · rw [heap]
    exact completion_channels graph layout state.heap logical.completed node channels
      stored.nodeDimension stored.channelDimension logical.completedUnique fresh
      stored.channelsUnique stored.channelLedger mapBound ledgerBound countBound
  · intro candidate
    have belowMap : layout.nodeMarkerBase + candidate.val < layout.mapBase := by
      have bound : candidate.val < layout.nodeCount := by rw [stored.nodeDimension]; exact candidate.isLt
      simp only [SharedLayout.mapBase]
      omega
    rw [heap, Array.getElem?_set_ne _ (by
      simp only [SharedLayout.nodeCountSlot, SharedLayout.mapBase] at belowMap ⊢
      omega), Array.getElem?_set_ne _ (by
      simp only [SharedLayout.nodeLedgerBase, SharedLayout.mapBase] at belowMap ⊢
      omega), Array.getElem?_set_ne _ (by omega)]
    simpa only [completeLogical_mark_set] using stored.flags candidate
  · intro candidate completed channel scopeMember
    change candidate ∈ logical.completed ++ [node] at completed
    rcases List.mem_append.mp completed with old | last
    · exact stored.completedScope candidate old channel scopeMember
    · have same : candidate = node := List.mem_singleton.mp last
      subst candidate
      exact scopeDone channel scopeMember
  · intro address beforeMarkers
    have beforeMap : layout.nodeMarkerBase ≤ layout.mapBase := by
      simp only [SharedLayout.mapBase]
      omega
    have beforeLedger : layout.nodeMarkerBase ≤ layout.nodeLedgerBase := by
      simp only [SharedLayout.nodeLedgerBase]
      omega
    have beforeCount : layout.nodeMarkerBase ≤ layout.nodeCountSlot := by
      simp only [SharedLayout.nodeCountSlot]
      omega
    rw [heap, Array.getElem?_set_ne _ (by omega),
      Array.getElem?_set_ne _ (by omega), Array.getElem?_set_ne _ (by omega)]


/-- One original root occurrence adds exactly45 fetched ticks around its body.
Publishing the root pays its own child/direct-scope overhead from the same
source-local weight as its descendants. -/
private theorem root_query_charge (graph : DAG n) (root : Fin graph.nodeCount)
    (descendants : List (Fin graph.nodeCount)) (bodyTicks : Nat)
    (bodyBound : bodyTicks ≤ 46 * freshWeight graph descendants +
      17 * (graph.node root).children.length +
      27 * (graph.node root).directChannels.length + 18) :
    bodyTicks + 45 ≤ 46 * freshWeight graph (descendants ++ [root]) + 17 := by
  have own : freshWeight graph [root] = localNodeWeight graph root := by simp [freshWeight]
  rw [freshWeight_append, own]
  simp only [localNodeWeight]
  omega

private theorem dfs_root_suspend_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 2) :
    (dfsFromCache width caller rows roots base layout)[6 + phase.val]? =
      (suspendCode)[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem dfs_root_touch_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 8) :
    (dfsFromCache width caller rows roots base layout)[8 + phase.val]? =
      (touchCode width layout.nodeMarkerBase (base + 8))[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private theorem dfs_root_resume_section (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat)
    (layout : SharedLayout) (phase : Fin 6) :
    (dfsFromCache width caller rows roots base layout)[114 + phase.val]? =
      (resumeCode width (base + 5))[phase.val]? := by
  fin_cases phase <;> simp [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc]

private structure RootCodeAt (program : Program width 8) (layout : SharedLayout)
    (base arity directory : Nat) : Prop where
  test : program[base + 5]? = some (.branchZero 4 (word width (base + 120)))
  suspend : ∀ phase : Fin 2, program[base + 6 + phase.val]? = suspendCode[phase.val]?
  touch : TouchAt program layout.nodeMarkerBase (base + 8)
  dispatch : program[base + 16]? = some (.branchZero 5 (word width (base + 18)))
  enter : ∀ phase : Fin 10, program[base + 18 + phase.val]? =
    (enterCode width arity directory)[phase.val]?
  finish : ∀ phase : Fin 13, program[base + 96 + phase.val]? =
    (finishLedgerCode width layout.nodeCountSlot layout.mapBase layout.nodeLedgerBase)[phase.val]?
  returnCode : ∀ phase : Fin 5, program[base + 109 + phase.val]? =
    (finishReturnCode width (base + 41) (base + 114))[phase.val]?
  resume : ∀ phase : Fin 6, program[base + 114 + phase.val]? =
    (resumeCode width (base + 5))[phase.val]?

private theorem fixed_root_code (program : Program width 8) (caller : Array (Word width))
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (base : Nat) (layout : SharedLayout)
    (physical : ∀ phase : Fin 120, program[base + phase.val]? =
      (dfsFromCache width caller rows roots base layout)[phase.val]?)
    (fits : base + 120 < 2 ^ width) :
    RootCodeAt program layout base (caller.size + 4 * rows.length) (caller.size + 2 * rows.length) := by
  have childCode := fixed_child_code program caller rows roots base layout physical fits
  refine ⟨?_, ?_, ?_, ?_, childCode.enterCodeAt, childCode.finishCodeAt, childCode.returnCodeAt, ?_⟩

  · simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using physical ⟨5, by decide⟩

  · intro phase
    have cell := physical ⟨6 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_root_suspend_section caller rows roots base layout phase)
  · intro phase
    have cell := physical ⟨8 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_root_touch_section caller rows roots base layout phase)

  · simpa [dfsFromCache, dfsProgram, suspendCode, touchCode, enterCode, resumeCode, nodeFrameCode, scopeTagCode, inputScopeCode, directoryCode, finishChannelCode, finishLedgerCode, finishReturnCode, rootTestOffset, rootSuspendOffset, rootTouchOffset, rootDispatchOffset, enterOffset, childTestOffset, childSuspendOffset, childTouchOffset, childDispatchOffset, childResumeOffset, scopeFrameOffset, scopeTagOffset, guardDirectoryOffset, guardJumpOffset, inputScopeOffset, inputJumpOffset, channelTestOffset, channelSuspendOffset, channelTouchOffset, channelDispatchOffset, channelPublishOffset, channelJumpOffset, channelResumeOffset, finishLedgerOffset, finishReturnOffset, rootResumeOffset, doneOffset, Nat.add_assoc] using physical ⟨16, by decide⟩

  · intro phase
    have cell := physical ⟨114 + phase.val, by have := phase.isLt; omega⟩
    simpa only [Nat.add_assoc] using cell.trans (dfs_root_resume_section caller rows roots base layout phase)

/-- One stored original root occurrence is extracted by the fixed fetched DFS.
The produced physical ledger is exactly its source cone in postorder. The
remaining-list recursion and smaller-ID node recursion are derived internally. -/
theorem root_query_execution
    (program : Program width 8) (graph : DAG n) (layout : SharedLayout)
    (caller : Array (Word width)) (rows : List ForestIndexedOperands.Row)
    (roots : List Nat) (base : Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (sourceSize : (ForestIndexedOperands.cacheHeap width caller rows roots).size = layout.sourceEnd)
    (physical : ∀ phase : Fin 120, program[base + phase.val]? =
      (dfsFromCache width caller rows roots base layout)[phase.val]?)
    (codeFits : base + 120 < 2 ^ width) (storageFits : layout.storageEnd < 2 ^ width)
    (slot : Fin graph.roots.length) (initial : State width 8) (before : DFSState graph)
    (emptyCompleted : before.completed = []) (emptyActive : before.active = [])
    (stored : TraversalStored graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
      initial before [])
    (position : initial.pc = word width (base + 5)) (running : initial.halted = false)
    (count : initial.reg 4 = word width 1)
    (cursorHeld : initial.reg 6 = word width (caller.size +
      (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
        (ForestIndexedOperands.rowGuards rows).length) + slot.val)) :
    ∃ (final : State width 8) (after : DFSState graph) (labels : List (Channel n)) (ticks peak : Nat),
      Execution program initial final ticks peak ∧
      ticks ≤ 46 * freshWeight graph after.completed + 17 ∧
      peak ≤ initial.liveWords + 3 * after.completed.length + 3 ∧
      TraversalStored graph layout (ForestIndexedOperands.cacheHeap width caller rows roots)
        final after labels ∧ after.active = [] ∧
      after.completed = discoverNode graph (graph.roots.get slot) [] ∧
      after.completed.toFinset = graph.cone (graph.roots.get slot) ∧
      Postorder graph after.completed ∧
      (∀ channel, channel ∈ labels ↔ channel ∈ graph.scope (graph.roots.get slot)) ∧
      (∀ address, address < layout.nodeMarkerBase → final.heap[address]? = initial.heap[address]?) ∧
      final.stack = initial.stack ∧ final.output = initial.output ∧
      final.reg 4 = word width 0 ∧
      final.reg 6 = word width (caller.size +
        (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
          (ForestIndexedOperands.rowGuards rows).length) + slot.val + 1) ∧
      final.reg 7 = word width 0 ∧ final.reg 2 = word width 0 ∧ final.reg 3 = word width 1 ∧
      final.pc = word width (base + 120) ∧ final.halted = false := by
  let root := graph.roots.get slot
  let cursor := caller.size + (6 * rows.length + (ForestIndexedOperands.rowChildren rows).length +
    (ForestIndexedOperands.rowGuards rows).length) + slot.val
  let source := ForestIndexedOperands.cacheHeap width caller rows roots
  have rootCode := fixed_root_code program caller rows roots base layout physical codeFits
  have sourceBound : cursor < source.size := by
    have lengths : roots.length = graph.roots.length := by rw [rootMatches, List.length_map]
    have valid := slot.isLt
    simp only [source, cursor, ForestIndexedOperands.cacheHeap_size]
    omega
  have beforeMarker : layout.sourceEnd ≤ layout.nodeMarkerBase := by
    simp only [SharedLayout.nodeMarkerBase]; omega
  have markerBelow : layout.nodeMarkerBase < layout.storageEnd := by
    simp only [SharedLayout.storageEnd, SharedLayout.nodeCountSlot]; omega
  have cursorFits : cursor + 1 < 2 ^ width := by rw [sourceSize] at sourceBound; omega
  have oneFits : 1 < 2 ^ width := by omega
  have heapBound : cursor < initial.heap.size := by
    rw [stored.allocation]
    rw [sourceSize] at sourceBound
    omega
  have sourceCell : initial.heap[cursor]'heapBound = word width root.val := by
    have original := ForestIndexedOperands.cache_declared_root_word caller graph rows roots rootMatches slot
    have cell := stored.sourceRetained ⟨cursor, sourceBound⟩
    have equal : initial.heap[cursor]? = some (word width root.val) :=
      cell.trans (congrArg some original)
    rw [Array.getElem?_eq_getElem heapBound] at equal
    exact Option.some.inj equal
  let tested := initial.advance
  have testTrace : Execution program initial tested 1 initial.liveWords := by
    simpa only [ite_false, Nat.one_ne_zero] using streamTest_execution program initial
      (base + 5) (base + 120) 1 rootCode.test position running (by omega) oneFits count
  have testedPosition : tested.pc = word width (base + 6) := by
    have entryFits : base + 5 < 2 ^ width := by omega
    change word width (initial.pc.val + 1) = word width (base + 6)
    rw [position, show (word width (base + 5)).val = base + 5 from Nat.mod_eq_of_lt entryFits]
  have testedStored : TraversalStored graph layout source tested before [] :=
    traversal_readonly graph layout source initial tested before [] stored rfl rfl rfl rfl
  have fresh : root ∉ before.completed := by rw [emptyCompleted]; exact List.not_mem_nil
  have inactive : root ∉ before.active := by rw [emptyActive]; exact List.not_mem_nil
  let metadata := retained_child_metadata caller tested.heap graph rows roots layout matched
    testedStored.sourceRetained sourceSize testedStored.allocation root
  obtain ⟨entered, enterTrace, enteredStored, enterValues, enterStack, enterOutput,
      enterCount, enterCursor, enterPosition, enterRunning⟩ :=
    child_fresh_global program graph layout source before tested [] root fresh inactive
      (base + 6) (base + 18) cursor 0 (caller.size + 4 * rows.length)
      (caller.size + 2 * rows.length) (graph.node root).children.length metadata.cursor
      rootCode.suspend rootCode.touch rootCode.dispatch rootCode.enter sourceSize testedStored
      testedPosition running (by omega) (by omega) storageFits
      (by simpa only [emptyActive, List.length_nil] using oneFits)
      cursorHeld count heapBound sourceCell metadata.arityBound metadata.directoryBound
      metadata.arityBeforeMarker metadata.directoryBeforeMarker metadata.arity metadata.directory
  let enteredLogical := activateChild graph before root fresh inactive
  have enteredActive : enteredLogical.active = root :: [] := by
    simp only [enteredLogical, activateChild, emptyActive]
  have above : AncestorsAbove graph root [] := by intro node member; exact False.elim (List.not_mem_nil member)
  obtain ⟨body⟩ := whole_node_body program graph layout caller rows roots base matched sourceSize
    physical codeFits storageFits root entered enteredLogical [] [] enteredStored enteredActive above
    (by simpa only [Nat.add_assoc] using enterPosition) enterRunning enterCount enterCursor
    ⟨word width cursor :: word width 1 :: initial.stack, enterStack⟩
  have bodyShape : body.logical.active = root :: [] := body.active.trans enteredActive
  obtain ⟨returned, finishTrace, returnedStored, returnedValues, returnedStack, returnedOutput,
      returnedCount, returnedCursor, returnedPosition, returnedRunning⟩ :=
    complete_root_global program graph layout source body.logical body.final body.channels root
      (base + 96) (base + 41) (base + 5) (base + 114) cursor 0 initial.stack
      rootCode.finish (by simpa only [Nat.add_assoc, Nat.reduceAdd] using rootCode.returnCode) rootCode.resume
      sourceSize body.stored bodyShape body.childDone body.ownScope body.position body.running
      (by omega) (by omega) (by omega) storageFits oneFits cursorFits oneFits
      (body.stack.trans enterStack)
  let after := completeLogical graph body.logical root [] bodyShape body.childDone
  let final : State width 8 := { returned.advance with pc := word width (base + 120) }
  have lastTrace : Execution program returned final 1 returned.liveWords := by
    simpa only [final, ite_true] using streamTest_execution program returned
      (base + 5) (base + 120) 0 rootCode.test returnedPosition returnedRunning
      (by omega) (by omega) returnedCount
  have finalStored : TraversalStored graph layout source final after body.channels :=
    traversal_readonly graph layout source returned final after body.channels returnedStored rfl rfl rfl rfl
  have enteredLive : entered.liveWords = initial.liveWords + 3 := by
    simp only [State.liveWords, enteredStored.allocation, stored.allocation,
      enterStack, enterOutput, List.length_cons, tested, State.advance]
    omega
  have returnedLive : returned.liveWords = initial.liveWords := by
    simp only [State.liveWords, returnedStored.allocation, stored.allocation, returnedStack,
      returnedOutput, body.output, enterOutput, tested, State.advance]
  have testedLive : tested.liveWords = initial.liveWords := rfl
  have bodyLower := body.execution.initial_storage_le
  have bodyUpper := body.execution.final_storage_le
  have ticksEqual : ((1 + 20 + body.ticks) + 23) + 1 = body.ticks + 45 := by omega
  have peakEqual : max (max (max (max initial.liveWords (tested.liveWords + 3)) body.peak)
      body.final.liveWords) returned.liveWords = body.peak := by omega
  have joined := (((testTrace.append enterTrace).append body.execution).append finishTrace).append lastTrace
  have tickTrace := Eq.mp (congrArg (fun ticks => Execution program initial final ticks
    (max (max (max (max initial.liveWords (tested.liveWords + 3)) body.peak)
      body.final.liveWords) returned.liveWords)) ticksEqual) joined
  have trace : Execution program initial final (body.ticks + 45) body.peak :=
    Eq.mp (congrArg (fun peak => Execution program initial final (body.ticks + 45) peak) peakEqual) tickTrace
  have beforeWeight : freshWeight graph enteredLogical.completed = 0 := by
    simp only [enteredLogical, activateChild, emptyCompleted, freshWeight, List.map_nil, List.sum_nil]
  have bodyBound : body.ticks ≤ 46 * freshWeight graph body.logical.completed +
      17 * (graph.node root).children.length + 27 * (graph.node root).directChannels.length + 18 := by
    simpa only [beforeWeight, Nat.mul_zero, Nat.add_zero] using body.charged
  have charged : body.ticks + 45 ≤ 46 * freshWeight graph after.completed + 17 :=
    root_query_charge graph root body.logical.completed body.ticks bodyBound
  have bodyDelta : body.peak ≤ entered.liveWords + 3 * body.logical.completed.length + 3 := by
    simpa only [enteredLogical, activateChild, emptyCompleted, List.length_nil, Nat.sub_zero] using body.deltaSpace
  have afterLength : after.completed.length = body.logical.completed.length + 1 := by
    simp only [after, completeLogical, List.length_append, List.length_singleton]
  have space : body.peak ≤ initial.liveWords + 3 * after.completed.length + 3 := by omega
  have bodyDiscovered : body.logical.completed = (graph.node root).children.foldl
      (fun completed child => discoverNode graph (graph.childIndex root child) completed) [] := by
    simpa only [enteredLogical, activateChild, emptyCompleted] using body.completed
  have discovered : after.completed = discoverNode graph root [] := by
    change body.logical.completed ++ [root] = _
    rw [discoverNode, ite_eq_right (List.not_mem_nil : root ∉ ([] : List (Fin graph.nodeCount)))]
    exact congrArg (fun completed => completed ++ [root]) bodyDiscovered
  have rootPresent : root ∈ after.completed := by
    simp only [after, completeLogical, List.mem_append, List.mem_singleton, or_true]
  have inside : ∀ node ∈ after.completed, node ∈ graph.cone root := by
    intro node member
    rcases List.mem_append.mp member with prior | last
    · rcases body.inside node prior with old | coneMember
      · exact False.elim (List.not_mem_nil (by
          simpa only [enteredLogical, activateChild, emptyCompleted] using old))
      · exact coneMember
    · have same : node = root := List.mem_singleton.mp last
      subst node
      exact graph.self_mem_cone root
  have cone := completed_eq_cone graph root after.completed rootPresent after.closed inside
  have emptyOrdered : Postorder graph enteredLogical.completed := by
    change Postorder graph before.completed
    rw [emptyCompleted]
    refine ⟨List.nodup_nil, ?_⟩
    intro position
    exact Fin.elim0 position
  have rootFresh : root ∉ body.logical.completed :=
    (List.disjoint_cons_right.mp (bodyShape ▸ body.logical.separate)).1
  have ordered : Postorder graph after.completed :=
    postorder_append_node graph body.logical.completed root (body.postorder emptyOrdered) rootFresh body.childDone
  have labelsExact : ∀ channel, channel ∈ body.channels ↔ channel ∈ graph.scope root := by
    intro channel
    simpa only [List.not_mem_nil, false_or] using body.channelsExact channel
  have values : ∀ address, address < layout.nodeMarkerBase → final.heap[address]? = initial.heap[address]? := by
    intro address below
    exact (returnedValues address below).trans ((body.values address below).trans (enterValues address below))
  have finalDepth : final.reg 7 = word width 0 := by
    simpa only [after, completeLogical, List.length_nil] using finalStored.depth
  refine ⟨final, after, body.channels, body.ticks + 45, body.peak, trace, charged, space,
    finalStored, rfl, discovered, cone, ordered, labelsExact, values, returnedStack, ?_,
    returnedCount, returnedCursor, finalDepth, finalStored.zero, finalStored.one, rfl, returnedRunning⟩
  exact returnedOutput.trans (body.output.trans enterOutput)

end Controller.Cost.SparseConeTraversal
