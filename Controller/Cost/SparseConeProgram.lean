module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGResources
public import Controller.Cost.ForestMarkerCollect

@[expose] public section

/-! Source-indexed marker access for sparse cone traversal. The incidence ID is
loaded from the retained packet before its separate marker cell is tested.
The first-touch store precedes publication on the work stack. -/
namespace Controller.Cost.SparseConeProgram
open Controller.Cost
variable {width : Nat}

/-- Register six holds an actual root/child/guard incidence cursor; registers
three and two hold one and zero. The same body serves node and channel markers. -/
def touchCode (width markerBase entry : Nat) : Program width 8 :=
  #[.load 0 6, .constant 1 (word width markerBase), .add 1 0 1,
    .load 5 1, .branchZero 5 (word width (entry + 6)),
    .branchZero 2 (word width (entry + 8)), .store 1 3, .push 0]

@[simp] theorem touch_code_size (width markerBase entry : Nat) :
    (touchCode width markerBase entry).size = 8 := rfl

def TouchAt (program : Program width 8) (markerBase entry : Nat) : Prop :=
  ∀ phase : Fin 8, program[entry + phase.val]? =
    (touchCode width markerBase entry)[phase.val]?

private theorem fetched (program : Program width 8) (state : State width 8)
    (entry : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (present : program[entry]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt fits, present]
  rfl

/-- A fresh physical incidence sets its marker before pushing the loaded ID.
The source cursor and all caller storage outside that one marker are retained. -/
theorem touch_fresh (program : Program width 8) (state : State width 8)
    (markerBase entry cursor identifier : Nat)
    (present : TouchAt program markerBase entry)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 8 < 2 ^ width)
    (cursorHeld : state.reg 6 = word width cursor) (cursorFits : cursor < 2 ^ width)
    (cursorBound : cursor < state.heap.size)
    (source : state.heap[cursor]'cursorBound = word width identifier)
    (markerFits : markerBase + identifier < 2 ^ width)
    (markerBound : markerBase + identifier < state.heap.size)
    (unmarked : state.heap[markerBase + identifier]'markerBound = word width 0)
    (one : state.reg 3 = word width 1) :
    ∃ final, Execution program state final 7 (state.liveWords + 1) ∧
      final.heap = state.heap.set (markerBase + identifier) (word width 1) markerBound ∧
      final.stack = word width identifier :: state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 8) ∧ final.halted = false ∧
      final.reg 6 = state.reg 6 ∧ final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧
      final.reg 4 = state.reg 4 ∧ final.reg 7 = state.reg 7 ∧
      final.reg 5 = word width 0 := by
  let s1 := state.advance.put 0 (word width identifier)
  let s2 := s1.advance.put 1 (word width markerBase)
  let s3 := s2.advance.put 1 (word width (markerBase + identifier))
  let s4 := s3.advance.put 5 (word width 0)
  let s5 : State width 8 := { s4.advance with pc := word width (entry + 6) }
  let s6 : State width 8 := { s5.advance with
    heap := state.heap.set (markerBase + identifier) (word width 1) markerBound }
  let final : State width 8 := { s6.advance with stack := word width identifier :: state.stack }
  have identifierVal : (word width identifier).val = identifier := Nat.mod_eq_of_lt (by omega)
  have markerBaseVal : (word width markerBase).val = markerBase := Nat.mod_eq_of_lt (by omega)
  have markerVal : (word width (markerBase + identifier)).val = markerBase + identifier := Nat.mod_eq_of_lt markerFits
  have zeroVal : (word width 0).val = 0 := by simp [word]
  have cursorVal : (word width cursor).val = cursor := Nat.mod_eq_of_lt cursorFits
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
  have p5 : s5.pc = word width (entry + 6) := rfl
  have p6 : s6.pc = word width (entry + 7) := by
    simp only [s6, State.advance, p5]
    rw [show (word width (entry + 6)).val = entry + 6 from Nat.mod_eq_of_lt (by omega)]
  have pf : final.pc = word width (entry + 8) := by
    simp only [final, State.advance, p6]
    rw [show (word width (entry + 7)).val = entry + 7 from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.load 0 6)
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [touchCode] using present ⟨0, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, final, State.put, State.advance,
      running, cursorHeld, cursorVal, cursorBound, source, identifierVal, markerBaseVal,
      markerVal, markerBound, unmarked, one, zeroVal, Nat.add_comm]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 1 (word width markerBase))
      (by simpa only [Nat.add_zero] using p1) (by omega)
      (by simpa [touchCode] using present ⟨1, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, final, State.put, State.advance,
      running, cursorHeld, cursorVal, cursorBound, source, identifierVal, markerBaseVal,
      markerVal, markerBound, unmarked, one, zeroVal, Nat.add_comm]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.add 1 0 1)
      (by simpa only [Nat.add_zero] using p2) (by omega)
      (by simpa [touchCode] using present ⟨2, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, final, State.put, State.advance,
      running, cursorHeld, cursorVal, cursorBound, source, identifierVal, markerBaseVal,
      markerVal, markerBound, unmarked, one, zeroVal, Nat.add_comm]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.load 5 1)
      (by simpa only [Nat.add_zero] using p3) (by omega)
      (by simpa [touchCode] using present ⟨3, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, final, State.put, State.advance,
      running, cursorHeld, cursorVal, cursorBound, source, identifierVal, markerBaseVal,
      markerVal, markerBound, unmarked, one, zeroVal, Nat.add_comm]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.branchZero 5 (word width (entry + 6)))
      (by simpa only [Nat.add_zero] using p4) (by omega)
      (by simpa [touchCode] using present ⟨4, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, final, State.put, State.advance,
      running, cursorHeld, cursorVal, cursorBound, source, identifierVal, markerBaseVal,
      markerVal, markerBound, unmarked, one, zeroVal, Nat.add_comm]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 6) (.store 1 3)
      (by simpa only [Nat.add_zero] using p5) (by omega)
      (by simpa [touchCode] using present ⟨6, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, final, State.put, State.advance,
      running, cursorHeld, cursorVal, cursorBound, source, identifierVal, markerBaseVal,
      markerVal, markerBound, unmarked, one, zeroVal, Nat.add_comm]
  have t6 : programStep program s6 = some final := by
    rw [fetched program s6 (entry + 7) (.push 0)
      (by simpa only [Nat.add_zero] using p6) (by omega)
      (by simpa [touchCode] using present ⟨7, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, s6, final, State.put, State.advance,
      running, cursorHeld, cursorVal, cursorBound, source, identifierVal, markerBaseVal,
      markerVal, markerBound, unmarked, one, zeroVal, Nat.add_comm]
  refine ⟨final, ?_, rfl, rfl, rfl, pf, running, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
      (Execution.cons t3 (Execution.cons t4 (Execution.cons t5
        (Execution.cons t6 (Execution.refl final)))))))
    have lf : final.liveWords = state.liveWords + 1 := by
      simp [final, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put]
      omega
    simpa only [show s1.liveWords = state.liveWords from rfl,
      show s2.liveWords = state.liveWords from rfl, show s3.liveWords = state.liveWords from rfl,
      show s4.liveWords = state.liveWords from rfl, show s5.liveWords = state.liveWords from rfl,
      show s6.liveWords = state.liveWords from by simp [s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put],
      lf, Nat.max_eq_right (by omega : state.liveWords ≤ state.liveWords + 1)] using trace
  all_goals simp [final, s6, s5, s4, s3, s2, s1, State.advance, State.put]

theorem touch_stale (program : Program width 8) (state : State width 8)
    (markerBase entry cursor identifier : Nat)
    (present : TouchAt program markerBase entry)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 8 < 2 ^ width)
    (cursorHeld : state.reg 6 = word width cursor) (cursorFits : cursor < 2 ^ width)
    (cursorBound : cursor < state.heap.size)
    (source : state.heap[cursor]'cursorBound = word width identifier)
    (markerFits : markerBase + identifier < 2 ^ width)
    (markerBound : markerBase + identifier < state.heap.size)
    (flag : Word width)
    (marked : state.heap[markerBase + identifier]'markerBound = flag)
    (nonzero : flag.val ≠ 0) (zero : state.reg 2 = word width 0) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 8) ∧ final.halted = false ∧
      final.reg 6 = state.reg 6 ∧ final.reg 2 = state.reg 2 ∧ final.reg 3 = state.reg 3 ∧
      final.reg 4 = state.reg 4 ∧ final.reg 7 = state.reg 7 ∧
      final.reg 5 = flag := by
  let s1 := state.advance.put 0 (word width identifier)
  let s2 := s1.advance.put 1 (word width markerBase)
  let s3 := s2.advance.put 1 (word width (markerBase + identifier))
  let s4 := s3.advance.put 5 flag
  let s5 := s4.advance
  let final : State width 8 := { s5.advance with pc := word width (entry + 8) }
  have identifierVal : (word width identifier).val = identifier := Nat.mod_eq_of_lt (by omega)
  have markerBaseVal : (word width markerBase).val = markerBase := Nat.mod_eq_of_lt (by omega)
  have markerVal : (word width (markerBase + identifier)).val = markerBase + identifier := Nat.mod_eq_of_lt markerFits
  have zeroVal : (word width 0).val = 0 := by simp [word]
  have cursorVal : (word width cursor).val = cursor := Nat.mod_eq_of_lt cursorFits
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
  have p5 : s5.pc = word width (entry + 5) := by
    simp only [s5, State.advance, p4]
    rw [show (word width (entry + 4)).val = entry + 4 from Nat.mod_eq_of_lt (by omega)]
  have pf : final.pc = word width (entry + 8) := rfl
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.load 0 6)
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [touchCode] using present ⟨0, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, cursorHeld, cursorVal, cursorBound, source, identifierVal, markerBaseVal,
      markerVal, markerBound, marked, zeroVal, Nat.add_comm]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 1 (word width markerBase))
      (by simpa only [Nat.add_zero] using p1) (by omega)
      (by simpa [touchCode] using present ⟨1, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, cursorHeld, cursorVal, cursorBound, source, identifierVal, markerBaseVal,
      markerVal, markerBound, marked, zeroVal, Nat.add_comm]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.add 1 0 1)
      (by simpa only [Nat.add_zero] using p2) (by omega)
      (by simpa [touchCode] using present ⟨2, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, cursorHeld, cursorVal, cursorBound, source, identifierVal, markerBaseVal,
      markerVal, markerBound, marked, zeroVal, Nat.add_comm]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.load 5 1)
      (by simpa only [Nat.add_zero] using p3) (by omega)
      (by simpa [touchCode] using present ⟨3, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, cursorHeld, cursorVal, cursorBound, source, identifierVal, markerBaseVal,
      markerVal, markerBound, marked, zeroVal, Nat.add_comm]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.branchZero 5 (word width (entry + 6))) p4 (by omega)
      (by simpa [touchCode] using present ⟨4, by decide⟩)]
    simp [step, s4, s3, s2, s1, s5, State.put, State.advance, running, nonzero]
  have t5 : programStep program s5 = some final := by
    rw [fetched program s5 (entry + 5) (.branchZero 2 (word width (entry + 8))) p5 (by omega)
      (by simpa [touchCode] using present ⟨5, by decide⟩)]
    simp [step, s5, s4, s3, s2, s1, final, State.put, State.advance, running, zero, zeroVal]
  refine ⟨final, ?_, rfl, rfl, rfl, pf, running, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
      (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl final))))))
    simpa only [show s1.liveWords = state.liveWords from rfl,
      show s2.liveWords = state.liveWords from rfl, show s3.liveWords = state.liveWords from rfl,
      show s4.liveWords = state.liveWords from rfl, show s5.liveWords = state.liveWords from rfl,
      show final.liveWords = state.liveWords from rfl, Nat.max_self] using trace
  all_goals simp [final, s5, s4, s3, s2, s1, State.advance, State.put]

/-- One fresh node enters with its source-loaded ID on top of the stack.
The current node ID remains below the child cursor/count continuation words. -/
def enterCode (width arityBase childDirectory : Nat) : Program width 8 :=
  #[.pop 0, .push 0, .add 7 7 3, .add 0 0 0,
    .constant 1 (word width arityBase), .add 1 1 0, .load 4 1,
    .constant 1 (word width childDirectory), .add 1 1 0, .load 6 1]

/-- Before the next child ID is loaded, the exact remaining count and source
cursor are saved. A fresh child returns here only after its postorder copy. -/
def suspendCode : Program width 8 := #[.push 4, .push 6]

def resumeCode (width loop : Nat) : Program width 8 :=
  #[.pop 6, .pop 4, .constant 5 (word width (2 ^ width - 1)),
    .add 4 4 5, .add 6 6 3, .branchZero 2 (word width loop)]

/-- Reading a directory uses the current node's doubled identity. Both
physical directories retain duplicate child and guard incidences. -/
def directoryCode (width arityBase sourceBase : Nat) : Program width 8 :=
  #[.constant 1 (word width arityBase), .add 1 1 0, .load 4 1,
    .constant 1 (word width sourceBase), .add 1 1 0, .load 6 1]

/-- The node identity is recovered from its charged frame before selecting
its guard directory; no abstract node query is an instruction. -/
def nodeFrameCode : Program width 8 := #[.pop 0, .push 0, .add 0 0 0]

/-- An original child occurrence is copied through its finished sparse map
entry. The source cursor and remaining count remain in registers six/four. -/
def copyChildCode (width oldToNewBase : Nat) : Program width 8 :=
  #[.load 0 6, .constant 1 (word width oldToNewBase), .add 0 0 1,
    .load 0 0, .allocate 0]

/-- Original guard occurrences retain their labels and multiplicities. -/
def copyGuardCode : Program width 8 := #[.load 0 6, .allocate 0]

/-- The fresh/stale marker result is still held in register five. Both touch
paths reach the same dispatch, but only the zero flag enters a fresh child. -/
def afterChildTouchCode (width enter resume : Nat) : Program width 8 :=
  #[.branchZero 5 (word width enter), .branchZero 2 (word width resume)]

@[simp] theorem directory_code_size (width arityBase sourceBase : Nat) :
    (directoryCode width arityBase sourceBase).size = 6 := rfl

/-- Actual indirect directory loads retain the suspended DFS node and caller
stack; the physical arity and base cells are the only source premises. -/
theorem directory_execution (program : Program width 8) (state : State width 8)
    (entry offset arityBase sourceBase count cursor : Nat)
    (present : ∀ phase : Fin 6, program[entry + phase.val]? =
      (directoryCode width arityBase sourceBase)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 6 < 2 ^ width) (offsetHeld : state.reg 0 = word width offset)
    (arityFits : arityBase + offset < 2 ^ width)
    (sourceFits : sourceBase + offset < 2 ^ width)
    (arityBound : arityBase + offset < state.heap.size)
    (sourceBound : sourceBase + offset < state.heap.size)
    (arityCell : state.heap[arityBase + offset]'arityBound = word width count)
    (sourceCell : state.heap[sourceBase + offset]'sourceBound = word width cursor) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      final.reg 4 = word width count ∧ final.reg 6 = word width cursor ∧
      final.reg 0 = state.reg 0 ∧ final.reg 2 = state.reg 2 ∧
      final.reg 3 = state.reg 3 ∧ final.reg 7 = state.reg 7 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 6) ∧ final.halted = false := by
  let s1 := state.advance.put 1 (word width arityBase)
  let s2 := s1.advance.put 1 (word width (arityBase + offset))
  let s3 := s2.advance.put 4 (word width count)
  let s4 := s3.advance.put 1 (word width sourceBase)
  let s5 := s4.advance.put 1 (word width (sourceBase + offset))
  let final := s5.advance.put 6 (word width cursor)
  have offsetVal : (word width offset).val = offset := Nat.mod_eq_of_lt (by omega)
  have arityBaseVal : (word width arityBase).val = arityBase := Nat.mod_eq_of_lt (by omega)
  have sourceBaseVal : (word width sourceBase).val = sourceBase := Nat.mod_eq_of_lt (by omega)
  have arityVal : (word width (arityBase + offset)).val = arityBase + offset := Nat.mod_eq_of_lt arityFits
  have sourceVal : (word width (sourceBase + offset)).val = sourceBase + offset := Nat.mod_eq_of_lt sourceFits
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
  have p6 : final.pc = word width (entry + 6) := by
    simp only [final, State.put, State.advance, p5]
    rw [show (word width (entry + 5)).val = (entry + 5) from Nat.mod_eq_of_lt (by omega)]
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.constant 1 (word width arityBase))
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [directoryCode] using present ⟨0, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, offsetHeld, offsetVal, arityBaseVal, sourceBaseVal, arityVal, sourceVal,
      arityBound, sourceBound, arityCell, sourceCell]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.add 1 1 0)
      (by simpa only [Nat.add_zero] using p1) (by omega)
      (by simpa [directoryCode] using present ⟨1, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, offsetHeld, offsetVal, arityBaseVal, sourceBaseVal, arityVal, sourceVal,
      arityBound, sourceBound, arityCell, sourceCell]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.load 4 1)
      (by simpa only [Nat.add_zero] using p2) (by omega)
      (by simpa [directoryCode] using present ⟨2, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, offsetHeld, offsetVal, arityBaseVal, sourceBaseVal, arityVal, sourceVal,
      arityBound, sourceBound, arityCell, sourceCell]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.constant 1 (word width sourceBase))
      (by simpa only [Nat.add_zero] using p3) (by omega)
      (by simpa [directoryCode] using present ⟨3, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, offsetHeld, offsetVal, arityBaseVal, sourceBaseVal, arityVal, sourceVal,
      arityBound, sourceBound, arityCell, sourceCell]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 1 1 0)
      (by simpa only [Nat.add_zero] using p4) (by omega)
      (by simpa [directoryCode] using present ⟨4, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, offsetHeld, offsetVal, arityBaseVal, sourceBaseVal, arityVal, sourceVal,
      arityBound, sourceBound, arityCell, sourceCell]
  have t5 : programStep program s5 = some final := by
    rw [fetched program s5 (entry + 5) (.load 6 1)
      (by simpa only [Nat.add_zero] using p5) (by omega)
      (by simpa [directoryCode] using present ⟨5, by decide⟩)]
    simp [step, s1, s2, s3, s4, s5, final, State.put, State.advance,
      running, offsetHeld, offsetVal, arityBaseVal, sourceBaseVal, arityVal, sourceVal,
      arityBound, sourceBound, arityCell, sourceCell]
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, p6, running⟩
  · have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
      (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl final))))))
    simpa only [show s1.liveWords = state.liveWords from rfl,
      show s2.liveWords = state.liveWords from rfl, show s3.liveWords = state.liveWords from rfl,
      show s4.liveWords = state.liveWords from rfl, show s5.liveWords = state.liveWords from rfl,
      show final.liveWords = state.liveWords from rfl, Nat.max_self] using trace
  all_goals simp [final, s5, s4, s3, s2, s1, State.advance, State.put]

end Controller.Cost.SparseConeProgram
