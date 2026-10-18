module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.RawAdapterProgram
public import Controller.Cost.RawTransferLoops
public import Controller.Cost.RawNumberingCounts
public import Controller.Horn.JoinedRuleFrame
public import Mathlib.Algebra.BigOperators.Fin

public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Controller.Cost.RawTypedCopy
open Controller.Cost
variable {width : Nat}
open Controller.Cost

theorem fetched (program : Program width 8) (state : State width 8)
    (address : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width address) (fits : address < 2 ^ width)
    (physical : program[address]? = some instruction) :
    programStep program state = step instruction state := by
  simp only [programStep, position, word, Nat.mod_eq_of_lt fits, physical]
  rfl


theorem marker_word_decrement (count : Nat) (positive : 0 < count)
    (fits : count < 2 ^ width) :
    word width (count + (2 ^ width - 1)) = word width (count - 1) := by
  apply Fin.ext
  change (count + (2 ^ width - 1)) % (2 ^ width) = (count - 1) % (2 ^ width)
  have split : count + (2 ^ width - 1) = count - 1 + 2 ^ width := by
    have nonzero := Nat.two_pow_pos width
    omega
  rw [split, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]


theorem referenceAdvancePC (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, word, Nat.mod_eq_of_lt fits]


-- Private helpers consumed only by the full original-source copy driver.
theorem copy_load_step (state : State width 8) (dst addressReg : Fin 8)
    (address : Nat) (value : Word width)
    (running : state.halted = false) (addressFits : address < 2 ^ width)
    (addressHeld : state.reg addressReg = word width address)
    (physical : state.heap[address]? = some value) :
    step (.load dst addressReg) state = some (state.advance.put dst value) := by
  obtain ⟨valid, cell⟩ := Array.getElem?_eq_some_iff.mp physical
  simp only [step, running, Bool.false_eq_true, ite_false, addressHeld,
    show (word width address).val = address from Nat.mod_eq_of_lt addressFits,
    dite_eq_left valid, cell]

theorem copy_allocate_step (state : State width 8) (src : Fin 8)
    (value : Word width) (running : state.halted = false)
    (room : state.heap.size < 2 ^ width) (held : state.reg src = value) :
    step (.allocate src) state = some { state.advance with heap := state.heap.push value } := by
  simp only [step, running, Bool.false_eq_true, ite_false, ite_eq_left room, held]

theorem copy_add_step (state : State width 8) (dst left right : Fin 8)
    (first second : Nat) (running : state.halted = false)
    (firstFits : first < 2 ^ width) (secondFits : second < 2 ^ width)
    (firstHeld : state.reg left = word width first) (secondHeld : state.reg right = word width second) :
    step (.add dst left right) state = some (state.advance.put dst (word width (first + second))) := by
  simp only [step, running, Bool.false_eq_true, ite_false, firstHeld, secondHeld,
    show (word width first).val = first from Nat.mod_eq_of_lt firstFits,
    show (word width second).val = second from Nat.mod_eq_of_lt secondFits]

theorem copy_xor_step (state : State width 8) (dst left right : Fin 8)
    (first second : Nat) (running : state.halted = false)
    (firstFits : first < 2 ^ width) (secondFits : second < 2 ^ width)
    (firstHeld : state.reg left = word width first) (secondHeld : state.reg right = word width second) :
    step (.xor dst left right) state = some (state.advance.put dst (word width (Nat.xor first second))) := by
  simp only [step, running, Bool.false_eq_true, ite_false, firstHeld, secondHeld,
    show (word width first).val = first from Nat.mod_eq_of_lt firstFits,
    show (word width second).val = second from Nat.mod_eq_of_lt secondFits]

theorem copy_branch_zero (state : State width 8) (src : Fin 8) (target : Nat)
    (running : state.halted = false) (zero : state.reg src = word width 0) :
    step (.branchZero src (word width target)) state =
      some { state.advance with pc := word width target } := by
  simp only [step, running, Bool.false_eq_true, ite_false, zero, word, Nat.zero_mod, ite_true]

theorem copy_branch_nonzero (state : State width 8) (src : Fin 8) (target value : Nat)
    (running : state.halted = false) (positive : 0 < value) (fits : value < 2 ^ width)
    (held : state.reg src = word width value) :
    step (.branchZero src (word width target)) state = some state.advance := by
  simp only [step, running, Bool.false_eq_true, ite_false, held,
    show (word width value).val = value from Nat.mod_eq_of_lt fits,
    ite_eq_right (by omega : value ≠ 0)]

-- Private concrete whole-copy consumer draft. Source encoder headers are
-- [tag,head] pairs; header origin 9 is relative to runtime raw packet base H.
-- ABI r0 remaining rows, r1 actual produced Q cursor, r4 actual rank base,
-- r6=0, r7=mask. Raw base H is read from the saved dead active header.
def typedHeaderCopyCode (width nodes base entry done : Nat) : Program width 8 :=
  #[.branchZero 0 (word width done),
    .constant 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)),
    .load 2 2,
    .load 3 1,
    .add 3 3 3,
    .add 2 2 3,
    .constant 5 (word width 9),
    .add 2 2 5,
    .load 5 2,
    .allocate 5,
    .add 3 5 6,
    .constant 5 (word width 1),
    .add 2 2 5,
    .branchZero 3 (word width (entry + 24)),
    .xor 3 3 5,
    .branchZero 3 (word width (entry + 24)),
    .constant 5 (word width 3),
    .xor 3 3 5,
    .branchZero 3 (word width (entry + 24)),
    .load 5 2,
    .add 5 5 4,
    .load 5 5,
    .allocate 5,
    .branchZero 6 (word width (entry + 27)),
    .load 5 2,
    .allocate 5,
    .branchZero 6 (word width (entry + 27)),
    .constant 3 (word width 1),
    .add 1 1 3,
    .add 0 0 7,
    .branchZero 6 (word width entry)]

-- Actual branch meanings:
-- tag0 passes source unused head0; tag1 passes exact original channel;
-- tag2 passes source unused head0; tag3/4 load mapped rank of guard/AND child.
-- tag xor1 xor3 = tag xor2, so the third test recognizes disjunction exactly.
-- Original constructors supply tag in0..4; this is a source-image theorem,
-- never an oracle inferred from an arbitrary word packet.
-- Per-row actual ticks: zero21, input23, disj26, guard/AND28; empty final1.
-- Allocates exactly 2V words, peak initial+2V, source/rank/Q unchanged.
-- Target rowHeaders of actual Q-numbered graph, retaining tag/head roles.
-- Row bases/arities and child/guard/root streams are subsequent fixed passes;
-- each reads the same actual Q cells and original stored source directories.


theorem copy_state_ext (left right : State width 8)
    (reg : ∀ register, left.reg register = right.reg register)
    (heap : left.heap = right.heap) (stack : left.stack = right.stack)
    (output : left.output = right.output) (pc : left.pc = right.pc)
    (halted : left.halted = right.halted) : left = right := by
  rcases left with ⟨lr, lh, ls, lo, lp, lb⟩
  rcases right with ⟨rr, rh, rs, ro, rp, rb⟩
  dsimp at reg heap stack output pc halted
  have registers := funext reg
  cases registers
  cases heap
  cases stack
  cases output
  cases pc
  cases halted
  rfl

theorem copy_constant_step (state : State width 8) (dst : Fin 8) (value : Word width)
    (running : state.halted = false) :
    step (.constant dst value) state = some (state.advance.put dst value) := by
  simp only [step, running, Bool.false_eq_true, ite_false]

theorem copy_push_cell (heap : Array (Word width)) (pushed value : Word width)
    (address : Nat) (cell : heap[address]? = some value) :
    (heap.push pushed)[address]? = some value := by
  obtain ⟨valid, actual⟩ := Array.getElem?_eq_some_iff.mp cell
  rw [Array.getElem?_eq_getElem (by simp only [Array.size_push]; omega),
    Array.getElem_push_lt valid, actual]

def copyRegisters (r0 r1 r2 r3 r4 r5 r6 r7 : Word width) : Fin 8 → Word width :=
  fun register => match register.val with
    | 0 => r0 | 1 => r1 | 2 => r2 | 3 => r3 | 4 => r4 | 5 => r5 | 6 => r6 | _ => r7

theorem copyRegisters_update0 (r0 r1 r2 r3 r4 r5 r6 r7 value : Word width) :
    (fun register => if register = 0 then value else copyRegisters r0 r1 r2 r3 r4 r5 r6 r7 register) =
      copyRegisters value r1 r2 r3 r4 r5 r6 r7 := by
  funext register
  fin_cases register <;> rfl

theorem copyRegisters_update1 (r0 r1 r2 r3 r4 r5 r6 r7 value : Word width) :
    (fun register => if register = 1 then value else copyRegisters r0 r1 r2 r3 r4 r5 r6 r7 register) =
      copyRegisters r0 value r2 r3 r4 r5 r6 r7 := by
  funext register
  fin_cases register <;> rfl

theorem copyRegisters_update2 (r0 r1 r2 r3 r4 r5 r6 r7 value : Word width) :
    (fun register => if register = 2 then value else copyRegisters r0 r1 r2 r3 r4 r5 r6 r7 register) =
      copyRegisters r0 r1 value r3 r4 r5 r6 r7 := by
  funext register
  fin_cases register <;> rfl

theorem copyRegisters_update3 (r0 r1 r2 r3 r4 r5 r6 r7 value : Word width) :
    (fun register => if register = 3 then value else copyRegisters r0 r1 r2 r3 r4 r5 r6 r7 register) =
      copyRegisters r0 r1 r2 value r4 r5 r6 r7 := by
  funext register
  fin_cases register <;> rfl

theorem copyRegisters_update4 (r0 r1 r2 r3 r4 r5 r6 r7 value : Word width) :
    (fun register => if register = 4 then value else copyRegisters r0 r1 r2 r3 r4 r5 r6 r7 register) =
      copyRegisters r0 r1 r2 r3 value r5 r6 r7 := by
  funext register
  fin_cases register <;> rfl

theorem copyRegisters_update5 (r0 r1 r2 r3 r4 r5 r6 r7 value : Word width) :
    (fun register => if register = 5 then value else copyRegisters r0 r1 r2 r3 r4 r5 r6 r7 register) =
      copyRegisters r0 r1 r2 r3 r4 value r6 r7 := by
  funext register
  fin_cases register <;> rfl

theorem copyRegisters_update6 (r0 r1 r2 r3 r4 r5 r6 r7 value : Word width) :
    (fun register => if register = 6 then value else copyRegisters r0 r1 r2 r3 r4 r5 r6 r7 register) =
      copyRegisters r0 r1 r2 r3 r4 r5 value r7 := by
  funext register
  fin_cases register <;> rfl

theorem copyRegisters_update7 (r0 r1 r2 r3 r4 r5 r6 r7 value : Word width) :
    (fun register => if register = 7 then value else copyRegisters r0 r1 r2 r3 r4 r5 r6 r7 register) =
      copyRegisters r0 r1 r2 r3 r4 r5 r6 value := by
  funext register
  fin_cases register <;> rfl

theorem copyRegisters_initial (state : State width 8) (count cursor rankBase : Nat)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (rankHeld : state.reg 4 = word width rankBase) (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1)) :
    state.reg = copyRegisters (word width count) (word width cursor) (state.reg 2) (state.reg 3)
      (word width rankBase) (state.reg 5) (word width 0) (word width (2 ^ width - 1)) := by
  funext register
  fin_cases register <;> simp [copyRegisters, countHeld, cursorHeld, rankHeld, zeroHeld, maskHeld]

theorem typed_header_case0_execution (resident : Program width 8)
    (nodes base entry done H old head rankBase cursor count : Nat) (mapped : Word width)
    (state : State width 8)
    (physical : ∀ phase : Fin 31, resident[entry + phase.val]? =
      (typedHeaderCopyCode width nodes base entry done)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 31 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width)
    (countFits : count < 2 ^ width) (positive : 0 < count)
    (cursorFits : cursor + 1 < 2 ^ width) (headFits : head < 2 ^ width)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (baseHeld : state.reg 4 = word width rankBase) (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (queueCell : state.heap[cursor]? = some (word width old))
    (tagCell : state.heap[H + 9 + 2 * old]? = some (word width 0))
    (headCell : state.heap[H + 9 + 2 * old + 1]? = some (word width head)) :
    ∃ final peak, Execution resident state final 21 peak ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = (state.heap.push (word width 0)).push (word width head) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  let s1 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 7) }
  let s8 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 8) }
  let s9 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (0)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 9) }
  let s10 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (0)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (0)), pc := word width (entry + 10) }
  let s11 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (0)) (word width (rankBase)) (word width (0)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (0)), pc := word width (entry + 11) }
  let s12 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (0)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (0)), pc := word width (entry + 12) }
  let s13 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (0)), pc := word width (entry + 13) }
  let s14 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (0)), pc := word width (entry + 24) }
  let s15 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (0)), pc := word width (entry + 25) }
  let s16 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (0))).push (word width (head)), pc := word width (entry + 26) }
  let s17 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (0))).push (word width (head)), pc := word width (entry + 27) }
  let s18 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (0))).push (word width (head)), pc := word width (entry + 28) }
  let s19 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (0))).push (word width (head)), pc := word width (entry + 29) }
  let s20 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (0))).push (word width (head)), pc := word width (entry + 30) }
  let s21 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (0))).push (word width (head)), pc := word width (entry + 0) }
  obtain ⟨rawBound, rawValue⟩ := Array.getElem?_eq_some_iff.mp rawCell
  obtain ⟨queueBound, queueValue⟩ := Array.getElem?_eq_some_iff.mp queueCell
  obtain ⟨tagBound, tagValue⟩ := Array.getElem?_eq_some_iff.mp tagCell
  obtain ⟨headBound, headValue⟩ := Array.getElem?_eq_some_iff.mp headCell
  have Hfits : H < 2 ^ width := by omega
  have oldFits : old < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.branchZero 0 (word width (done))) position (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨0, by decide⟩)]
    have result := copy_branch_nonzero state 0 (done) (count) running (by omega) (by omega) (by simp [countHeld, cursorHeld, baseHeld, zeroHeld, maskHeld])
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_initial state count cursor rankBase
        countHeld cursorHeld baseHeld zeroHeld maskHeld) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s1, State.liveWords, Array.size_push] <;> omega
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨1, by decide⟩)]
    have result := copy_constant_step s1 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s2, State.liveWords, Array.size_push] <;> omega
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.load 2 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨2, by decide⟩)]
    have result := copy_load_step s2 2 2 (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base) (word width (H)) running (by omega) (by rfl) (by change state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width (H)); exact rawCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords + 0 := by
    simp only [s3, State.liveWords, Array.size_push] <;> omega
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.load 3 1) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨3, by decide⟩)]
    have result := copy_load_step s3 3 1 (cursor) (word width (old)) running (by omega) (by rfl) (by change state.heap[cursor]? = some (word width (old)); exact queueCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (old))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords + 0 := by
    simp only [s4, State.liveWords, Array.size_push] <;> omega
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.add 3 3 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨4, by decide⟩)]
    have result := copy_add_step s4 3 3 3 (old) (old) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (old) + (old) = (2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords + 0 := by
    simp only [s5, State.liveWords, Array.size_push] <;> omega
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.add 2 2 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨5, by decide⟩)]
    have result := copy_add_step s5 2 2 3 (H) (2 * old) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H) + (2 * old) = (H + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords + 0 := by
    simp only [s6, State.liveWords, Array.size_push] <;> omega
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 5 (word width (9))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨6, by decide⟩)]
    have result := copy_constant_step s6 5 (word width (9)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (9))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords + 0 := by
    simp only [s7, State.liveWords, Array.size_push] <;> omega
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨7, by decide⟩)]
    have result := copy_add_step s7 2 2 5 (H + 2 * old) (9) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H + 2 * old) + (9) = (H + 9 + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 9 + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords + 0 := by
    simp only [s8, State.liveWords, Array.size_push] <;> omega
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨8, by decide⟩)]
    have result := copy_load_step s8 5 2 (H + 9 + 2 * old) (word width (0)) running (by omega) (by rfl) (by change state.heap[H + 9 + 2 * old]? = some (word width (0)); exact tagCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1)) (word width (0))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords + 0 := by
    simp only [s9, State.liveWords, Array.size_push] <;> omega
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨9, by decide⟩)]
    have result := copy_allocate_step s9 5 (word width (0)) running (by simp only [s9, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords + 1 := by
    simp only [s10, State.liveWords, Array.size_push] <;> omega
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.add 3 5 6) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨10, by decide⟩)]
    have result := copy_add_step s10 3 5 6 (0) (0) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (0) + (0) = (0) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (0)) (word width (0)) (word width (2 ^ width - 1)) (word width (0))) register
    · rfl
    · rfl
    · rfl
    · change s10.advance.pc = word width (entry + 11)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s10
        (entry + 10) (by rfl) (by omega)
    · rfl
  have live11 : s11.liveWords = state.liveWords + 1 := by
    simp only [s11, State.liveWords, Array.size_push] <;> omega
  have t11 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.constant 5 (word width (1))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨11, by decide⟩)]
    have result := copy_constant_step s11 5 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (0)) (word width (rankBase)) (word width (0)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s11.advance.pc = word width (entry + 12)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s11
        (entry + 11) (by rfl) (by omega)
    · rfl
  have live12 : s12.liveWords = state.liveWords + 1 := by
    simp only [s12, State.liveWords, Array.size_push] <;> omega
  have t12 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨12, by decide⟩)]
    have result := copy_add_step s12 2 2 5 (H + 9 + 2 * old) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H + 9 + 2 * old) + (1) = (H + 9 + 2 * old + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (0)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 9 + 2 * old + 1))) register
    · rfl
    · rfl
    · rfl
    · change s12.advance.pc = word width (entry + 13)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s12
        (entry + 12) (by rfl) (by omega)
    · rfl
  have live13 : s13.liveWords = state.liveWords + 1 := by
    simp only [s13, State.liveWords, Array.size_push] <;> omega
  have t13 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨13, by decide⟩)]
    have result := copy_branch_zero s13 3 (entry + 24) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live14 : s14.liveWords = state.liveWords + 1 := by
    simp only [s14, State.liveWords, Array.size_push] <;> omega
  have t14 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 24) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨24, by decide⟩)]
    have result := copy_load_step s14 5 2 (H + 9 + 2 * old + 1) (word width (head)) running (by omega) (by rfl) (by change (state.heap.push (word width 0))[H + 9 + 2 * old + 1]? = some (word width (head)); exact copy_push_cell state.heap _ _ _ headCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (head))) register
    · rfl
    · rfl
    · rfl
    · change s14.advance.pc = word width (entry + 25)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s14
        (entry + 24) (by rfl) (by omega)
    · rfl
  have live15 : s15.liveWords = state.liveWords + 1 := by
    simp only [s15, State.liveWords, Array.size_push] <;> omega
  have t15 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 25) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨25, by decide⟩)]
    have result := copy_allocate_step s15 5 (word width (head)) running (by simp only [s15, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s15.advance.pc = word width (entry + 26)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s15
        (entry + 25) (by rfl) (by omega)
    · rfl
  have live16 : s16.liveWords = state.liveWords + 2 := by
    simp only [s16, State.liveWords, Array.size_push] <;> omega
  have t16 : programStep resident s16 = some s17 := by
    rw [fetched resident s16 (entry + 26) (.branchZero 6 (word width (entry + 27))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨26, by decide⟩)]
    have result := copy_branch_zero s16 6 (entry + 27) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live17 : s17.liveWords = state.liveWords + 2 := by
    simp only [s17, State.liveWords, Array.size_push] <;> omega
  have t17 : programStep resident s17 = some s18 := by
    rw [fetched resident s17 (entry + 27) (.constant 3 (word width (1))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨27, by decide⟩)]
    have result := copy_constant_step s17 3 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s17.advance.pc = word width (entry + 28)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s17
        (entry + 27) (by rfl) (by omega)
    · rfl
  have live18 : s18.liveWords = state.liveWords + 2 := by
    simp only [s18, State.liveWords, Array.size_push] <;> omega
  have t18 : programStep resident s18 = some s19 := by
    rw [fetched resident s18 (entry + 28) (.add 1 1 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨28, by decide⟩)]
    have result := copy_add_step s18 1 1 3 (cursor) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (cursor) + (1) = (cursor + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1)) (word width (cursor + 1))) register
    · rfl
    · rfl
    · rfl
    · change s18.advance.pc = word width (entry + 29)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s18
        (entry + 28) (by rfl) (by omega)
    · rfl
  have live19 : s19.liveWords = state.liveWords + 2 := by
    simp only [s19, State.liveWords, Array.size_push] <;> omega
  have t19 : programStep resident s19 = some s20 := by
    rw [fetched resident s19 (entry + 29) (.add 0 0 7) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨29, by decide⟩)]
    have result := copy_add_step s19 0 0 7 (count) (2 ^ width - 1) running (by omega) (by omega) (by rfl) (by rfl)
    rw [marker_word_decrement count positive countFits] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (count)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1)) (word width (count - 1))) register
    · rfl
    · rfl
    · rfl
    · change s19.advance.pc = word width (entry + 30)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s19
        (entry + 29) (by rfl) (by omega)
    · rfl
  have live20 : s20.liveWords = state.liveWords + 2 := by
    simp only [s20, State.liveWords, Array.size_push] <;> omega
  have t20 : programStep resident s20 = some s21 := by
    rw [fetched resident s20 (entry + 30) (.branchZero 6 (word width (entry))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨30, by decide⟩)]
    have result := copy_branch_zero s20 6 (entry) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live21 : s21.liveWords = state.liveWords + 2 := by
    simp only [s21, State.liveWords, Array.size_push] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.cons t16 (Execution.cons t17 (Execution.cons t18 (Execution.cons t19 (Execution.cons t20 (Execution.refl s21)))))))))))))))))))))
  refine ⟨s21, max state.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords (max s4.liveWords (max s5.liveWords (max s6.liveWords (max s7.liveWords (max s8.liveWords (max s9.liveWords (max s10.liveWords (max s11.liveWords (max s12.liveWords (max s13.liveWords (max s14.liveWords (max s15.liveWords (max s16.liveWords (max s17.liveWords (max s18.liveWords (max s19.liveWords (max s20.liveWords (s21.liveWords))))))))))))))))))))), ?_, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.reduceAdd] using trace
  · simp only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, live14, live15, live16, live17, live18, live19, live20, live21, max_le_iff]
    omega
  · rfl
  · rfl
  · exact baseHeld.symm
  · exact zeroHeld.symm
  · exact maskHeld.symm

theorem typed_header_case1_execution (resident : Program width 8)
    (nodes base entry done H old head rankBase cursor count : Nat) (mapped : Word width)
    (state : State width 8)
    (physical : ∀ phase : Fin 31, resident[entry + phase.val]? =
      (typedHeaderCopyCode width nodes base entry done)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 31 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width)
    (countFits : count < 2 ^ width) (positive : 0 < count)
    (cursorFits : cursor + 1 < 2 ^ width) (headFits : head < 2 ^ width)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (baseHeld : state.reg 4 = word width rankBase) (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (queueCell : state.heap[cursor]? = some (word width old))
    (tagCell : state.heap[H + 9 + 2 * old]? = some (word width 1))
    (headCell : state.heap[H + 9 + 2 * old + 1]? = some (word width head)) :
    ∃ final peak, Execution resident state final 23 peak ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = (state.heap.push (word width 1)).push (word width head) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  let s1 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 7) }
  let s8 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 8) }
  let s9 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 9) }
  let s10 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (1)), pc := word width (entry + 10) }
  let s11 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (1)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (1)), pc := word width (entry + 11) }
  let s12 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (1)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (1)), pc := word width (entry + 12) }
  let s13 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (1)), pc := word width (entry + 13) }
  let s14 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (1)), pc := word width (entry + 14) }
  let s15 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (1)), pc := word width (entry + 15) }
  let s16 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (1)), pc := word width (entry + 24) }
  let s17 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (1)), pc := word width (entry + 25) }
  let s18 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (1))).push (word width (head)), pc := word width (entry + 26) }
  let s19 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (1))).push (word width (head)), pc := word width (entry + 27) }
  let s20 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (1))).push (word width (head)), pc := word width (entry + 28) }
  let s21 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (1))).push (word width (head)), pc := word width (entry + 29) }
  let s22 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (1))).push (word width (head)), pc := word width (entry + 30) }
  let s23 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (1))).push (word width (head)), pc := word width (entry + 0) }
  obtain ⟨rawBound, rawValue⟩ := Array.getElem?_eq_some_iff.mp rawCell
  obtain ⟨queueBound, queueValue⟩ := Array.getElem?_eq_some_iff.mp queueCell
  obtain ⟨tagBound, tagValue⟩ := Array.getElem?_eq_some_iff.mp tagCell
  obtain ⟨headBound, headValue⟩ := Array.getElem?_eq_some_iff.mp headCell
  have Hfits : H < 2 ^ width := by omega
  have oldFits : old < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.branchZero 0 (word width (done))) position (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨0, by decide⟩)]
    have result := copy_branch_nonzero state 0 (done) (count) running (by omega) (by omega) (by simp [countHeld, cursorHeld, baseHeld, zeroHeld, maskHeld])
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_initial state count cursor rankBase
        countHeld cursorHeld baseHeld zeroHeld maskHeld) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s1, State.liveWords, Array.size_push] <;> omega
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨1, by decide⟩)]
    have result := copy_constant_step s1 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s2, State.liveWords, Array.size_push] <;> omega
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.load 2 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨2, by decide⟩)]
    have result := copy_load_step s2 2 2 (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base) (word width (H)) running (by omega) (by rfl) (by change state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width (H)); exact rawCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords + 0 := by
    simp only [s3, State.liveWords, Array.size_push] <;> omega
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.load 3 1) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨3, by decide⟩)]
    have result := copy_load_step s3 3 1 (cursor) (word width (old)) running (by omega) (by rfl) (by change state.heap[cursor]? = some (word width (old)); exact queueCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (old))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords + 0 := by
    simp only [s4, State.liveWords, Array.size_push] <;> omega
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.add 3 3 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨4, by decide⟩)]
    have result := copy_add_step s4 3 3 3 (old) (old) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (old) + (old) = (2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords + 0 := by
    simp only [s5, State.liveWords, Array.size_push] <;> omega
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.add 2 2 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨5, by decide⟩)]
    have result := copy_add_step s5 2 2 3 (H) (2 * old) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H) + (2 * old) = (H + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords + 0 := by
    simp only [s6, State.liveWords, Array.size_push] <;> omega
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 5 (word width (9))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨6, by decide⟩)]
    have result := copy_constant_step s6 5 (word width (9)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (9))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords + 0 := by
    simp only [s7, State.liveWords, Array.size_push] <;> omega
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨7, by decide⟩)]
    have result := copy_add_step s7 2 2 5 (H + 2 * old) (9) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H + 2 * old) + (9) = (H + 9 + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 9 + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords + 0 := by
    simp only [s8, State.liveWords, Array.size_push] <;> omega
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨8, by decide⟩)]
    have result := copy_load_step s8 5 2 (H + 9 + 2 * old) (word width (1)) running (by omega) (by rfl) (by change state.heap[H + 9 + 2 * old]? = some (word width (1)); exact tagCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords + 0 := by
    simp only [s9, State.liveWords, Array.size_push] <;> omega
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨9, by decide⟩)]
    have result := copy_allocate_step s9 5 (word width (1)) running (by simp only [s9, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords + 1 := by
    simp only [s10, State.liveWords, Array.size_push] <;> omega
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.add 3 5 6) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨10, by decide⟩)]
    have result := copy_add_step s10 3 5 6 (1) (0) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (1) + (0) = (1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s10.advance.pc = word width (entry + 11)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s10
        (entry + 10) (by rfl) (by omega)
    · rfl
  have live11 : s11.liveWords = state.liveWords + 1 := by
    simp only [s11, State.liveWords, Array.size_push] <;> omega
  have t11 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.constant 5 (word width (1))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨11, by decide⟩)]
    have result := copy_constant_step s11 5 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (1)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s11.advance.pc = word width (entry + 12)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s11
        (entry + 11) (by rfl) (by omega)
    · rfl
  have live12 : s12.liveWords = state.liveWords + 1 := by
    simp only [s12, State.liveWords, Array.size_push] <;> omega
  have t12 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨12, by decide⟩)]
    have result := copy_add_step s12 2 2 5 (H + 9 + 2 * old) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H + 9 + 2 * old) + (1) = (H + 9 + 2 * old + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (1)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 9 + 2 * old + 1))) register
    · rfl
    · rfl
    · rfl
    · change s12.advance.pc = word width (entry + 13)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s12
        (entry + 12) (by rfl) (by omega)
    · rfl
  have live13 : s13.liveWords = state.liveWords + 1 := by
    simp only [s13, State.liveWords, Array.size_push] <;> omega
  have t13 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨13, by decide⟩)]
    have result := copy_branch_nonzero s13 3 (entry + 24) (1) running (by omega) (by omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s13.advance.pc = word width (entry + 14)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s13
        (entry + 13) (by rfl) (by omega)
    · rfl
  have live14 : s14.liveWords = state.liveWords + 1 := by
    simp only [s14, State.liveWords, Array.size_push] <;> omega
  have t14 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 14) (.xor 3 3 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨14, by decide⟩)]
    have result := copy_xor_step s14 3 3 5 (1) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : Nat.xor (1) (1) = (0) := by decide
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (0))) register
    · rfl
    · rfl
    · rfl
    · change s14.advance.pc = word width (entry + 15)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s14
        (entry + 14) (by rfl) (by omega)
    · rfl
  have live15 : s15.liveWords = state.liveWords + 1 := by
    simp only [s15, State.liveWords, Array.size_push] <;> omega
  have t15 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 15) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨15, by decide⟩)]
    have result := copy_branch_zero s15 3 (entry + 24) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live16 : s16.liveWords = state.liveWords + 1 := by
    simp only [s16, State.liveWords, Array.size_push] <;> omega
  have t16 : programStep resident s16 = some s17 := by
    rw [fetched resident s16 (entry + 24) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨24, by decide⟩)]
    have result := copy_load_step s16 5 2 (H + 9 + 2 * old + 1) (word width (head)) running (by omega) (by rfl) (by change (state.heap.push (word width 1))[H + 9 + 2 * old + 1]? = some (word width (head)); exact copy_push_cell state.heap _ _ _ headCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (head))) register
    · rfl
    · rfl
    · rfl
    · change s16.advance.pc = word width (entry + 25)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s16
        (entry + 24) (by rfl) (by omega)
    · rfl
  have live17 : s17.liveWords = state.liveWords + 1 := by
    simp only [s17, State.liveWords, Array.size_push] <;> omega
  have t17 : programStep resident s17 = some s18 := by
    rw [fetched resident s17 (entry + 25) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨25, by decide⟩)]
    have result := copy_allocate_step s17 5 (word width (head)) running (by simp only [s17, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s17.advance.pc = word width (entry + 26)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s17
        (entry + 25) (by rfl) (by omega)
    · rfl
  have live18 : s18.liveWords = state.liveWords + 2 := by
    simp only [s18, State.liveWords, Array.size_push] <;> omega
  have t18 : programStep resident s18 = some s19 := by
    rw [fetched resident s18 (entry + 26) (.branchZero 6 (word width (entry + 27))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨26, by decide⟩)]
    have result := copy_branch_zero s18 6 (entry + 27) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live19 : s19.liveWords = state.liveWords + 2 := by
    simp only [s19, State.liveWords, Array.size_push] <;> omega
  have t19 : programStep resident s19 = some s20 := by
    rw [fetched resident s19 (entry + 27) (.constant 3 (word width (1))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨27, by decide⟩)]
    have result := copy_constant_step s19 3 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s19.advance.pc = word width (entry + 28)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s19
        (entry + 27) (by rfl) (by omega)
    · rfl
  have live20 : s20.liveWords = state.liveWords + 2 := by
    simp only [s20, State.liveWords, Array.size_push] <;> omega
  have t20 : programStep resident s20 = some s21 := by
    rw [fetched resident s20 (entry + 28) (.add 1 1 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨28, by decide⟩)]
    have result := copy_add_step s20 1 1 3 (cursor) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (cursor) + (1) = (cursor + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1)) (word width (cursor + 1))) register
    · rfl
    · rfl
    · rfl
    · change s20.advance.pc = word width (entry + 29)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s20
        (entry + 28) (by rfl) (by omega)
    · rfl
  have live21 : s21.liveWords = state.liveWords + 2 := by
    simp only [s21, State.liveWords, Array.size_push] <;> omega
  have t21 : programStep resident s21 = some s22 := by
    rw [fetched resident s21 (entry + 29) (.add 0 0 7) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨29, by decide⟩)]
    have result := copy_add_step s21 0 0 7 (count) (2 ^ width - 1) running (by omega) (by omega) (by rfl) (by rfl)
    rw [marker_word_decrement count positive countFits] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (count)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1)) (word width (count - 1))) register
    · rfl
    · rfl
    · rfl
    · change s21.advance.pc = word width (entry + 30)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s21
        (entry + 29) (by rfl) (by omega)
    · rfl
  have live22 : s22.liveWords = state.liveWords + 2 := by
    simp only [s22, State.liveWords, Array.size_push] <;> omega
  have t22 : programStep resident s22 = some s23 := by
    rw [fetched resident s22 (entry + 30) (.branchZero 6 (word width (entry))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨30, by decide⟩)]
    have result := copy_branch_zero s22 6 (entry) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live23 : s23.liveWords = state.liveWords + 2 := by
    simp only [s23, State.liveWords, Array.size_push] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.cons t16 (Execution.cons t17 (Execution.cons t18 (Execution.cons t19 (Execution.cons t20 (Execution.cons t21 (Execution.cons t22 (Execution.refl s23)))))))))))))))))))))))
  refine ⟨s23, max state.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords (max s4.liveWords (max s5.liveWords (max s6.liveWords (max s7.liveWords (max s8.liveWords (max s9.liveWords (max s10.liveWords (max s11.liveWords (max s12.liveWords (max s13.liveWords (max s14.liveWords (max s15.liveWords (max s16.liveWords (max s17.liveWords (max s18.liveWords (max s19.liveWords (max s20.liveWords (max s21.liveWords (max s22.liveWords (s23.liveWords))))))))))))))))))))))), ?_, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.reduceAdd] using trace
  · simp only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, live14, live15, live16, live17, live18, live19, live20, live21, live22, live23, max_le_iff]
    omega
  · rfl
  · rfl
  · exact baseHeld.symm
  · exact zeroHeld.symm
  · exact maskHeld.symm

theorem typed_header_case2_execution (resident : Program width 8)
    (nodes base entry done H old head rankBase cursor count : Nat) (mapped : Word width)
    (state : State width 8)
    (physical : ∀ phase : Fin 31, resident[entry + phase.val]? =
      (typedHeaderCopyCode width nodes base entry done)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 31 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width)
    (countFits : count < 2 ^ width) (positive : 0 < count)
    (cursorFits : cursor + 1 < 2 ^ width) (headFits : head < 2 ^ width)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (baseHeld : state.reg 4 = word width rankBase) (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (queueCell : state.heap[cursor]? = some (word width old))
    (tagCell : state.heap[H + 9 + 2 * old]? = some (word width 2))
    (headCell : state.heap[H + 9 + 2 * old + 1]? = some (word width head)) :
    ∃ final peak, Execution resident state final 26 peak ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = (state.heap.push (word width 2)).push (word width head) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  let s1 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 7) }
  let s8 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 8) }
  let s9 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (2)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 9) }
  let s10 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (2)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (2)), pc := word width (entry + 10) }
  let s11 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2)) (word width (rankBase)) (word width (2)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (2)), pc := word width (entry + 11) }
  let s12 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (2)), pc := word width (entry + 12) }
  let s13 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (2)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (2)), pc := word width (entry + 13) }
  let s14 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (2)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (2)), pc := word width (entry + 14) }
  let s15 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (3)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (2)), pc := word width (entry + 15) }
  let s16 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (3)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (2)), pc := word width (entry + 16) }
  let s17 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (3)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (2)), pc := word width (entry + 17) }
  let s18 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (2)), pc := word width (entry + 18) }
  let s19 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (2)), pc := word width (entry + 24) }
  let s20 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (2)), pc := word width (entry + 25) }
  let s21 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (2))).push (word width (head)), pc := word width (entry + 26) }
  let s22 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (2))).push (word width (head)), pc := word width (entry + 27) }
  let s23 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (2))).push (word width (head)), pc := word width (entry + 28) }
  let s24 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (2))).push (word width (head)), pc := word width (entry + 29) }
  let s25 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (2))).push (word width (head)), pc := word width (entry + 30) }
  let s26 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (2))).push (word width (head)), pc := word width (entry + 0) }
  obtain ⟨rawBound, rawValue⟩ := Array.getElem?_eq_some_iff.mp rawCell
  obtain ⟨queueBound, queueValue⟩ := Array.getElem?_eq_some_iff.mp queueCell
  obtain ⟨tagBound, tagValue⟩ := Array.getElem?_eq_some_iff.mp tagCell
  obtain ⟨headBound, headValue⟩ := Array.getElem?_eq_some_iff.mp headCell
  have Hfits : H < 2 ^ width := by omega
  have oldFits : old < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.branchZero 0 (word width (done))) position (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨0, by decide⟩)]
    have result := copy_branch_nonzero state 0 (done) (count) running (by omega) (by omega) (by simp [countHeld, cursorHeld, baseHeld, zeroHeld, maskHeld])
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_initial state count cursor rankBase
        countHeld cursorHeld baseHeld zeroHeld maskHeld) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s1, State.liveWords, Array.size_push] <;> omega
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨1, by decide⟩)]
    have result := copy_constant_step s1 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s2, State.liveWords, Array.size_push] <;> omega
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.load 2 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨2, by decide⟩)]
    have result := copy_load_step s2 2 2 (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base) (word width (H)) running (by omega) (by rfl) (by change state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width (H)); exact rawCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords + 0 := by
    simp only [s3, State.liveWords, Array.size_push] <;> omega
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.load 3 1) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨3, by decide⟩)]
    have result := copy_load_step s3 3 1 (cursor) (word width (old)) running (by omega) (by rfl) (by change state.heap[cursor]? = some (word width (old)); exact queueCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (old))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords + 0 := by
    simp only [s4, State.liveWords, Array.size_push] <;> omega
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.add 3 3 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨4, by decide⟩)]
    have result := copy_add_step s4 3 3 3 (old) (old) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (old) + (old) = (2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords + 0 := by
    simp only [s5, State.liveWords, Array.size_push] <;> omega
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.add 2 2 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨5, by decide⟩)]
    have result := copy_add_step s5 2 2 3 (H) (2 * old) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H) + (2 * old) = (H + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords + 0 := by
    simp only [s6, State.liveWords, Array.size_push] <;> omega
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 5 (word width (9))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨6, by decide⟩)]
    have result := copy_constant_step s6 5 (word width (9)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (9))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords + 0 := by
    simp only [s7, State.liveWords, Array.size_push] <;> omega
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨7, by decide⟩)]
    have result := copy_add_step s7 2 2 5 (H + 2 * old) (9) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H + 2 * old) + (9) = (H + 9 + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 9 + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords + 0 := by
    simp only [s8, State.liveWords, Array.size_push] <;> omega
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨8, by decide⟩)]
    have result := copy_load_step s8 5 2 (H + 9 + 2 * old) (word width (2)) running (by omega) (by rfl) (by change state.heap[H + 9 + 2 * old]? = some (word width (2)); exact tagCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1)) (word width (2))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords + 0 := by
    simp only [s9, State.liveWords, Array.size_push] <;> omega
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨9, by decide⟩)]
    have result := copy_allocate_step s9 5 (word width (2)) running (by simp only [s9, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords + 1 := by
    simp only [s10, State.liveWords, Array.size_push] <;> omega
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.add 3 5 6) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨10, by decide⟩)]
    have result := copy_add_step s10 3 5 6 (2) (0) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (2) + (0) = (2) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (2)) (word width (0)) (word width (2 ^ width - 1)) (word width (2))) register
    · rfl
    · rfl
    · rfl
    · change s10.advance.pc = word width (entry + 11)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s10
        (entry + 10) (by rfl) (by omega)
    · rfl
  have live11 : s11.liveWords = state.liveWords + 1 := by
    simp only [s11, State.liveWords, Array.size_push] <;> omega
  have t11 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.constant 5 (word width (1))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨11, by decide⟩)]
    have result := copy_constant_step s11 5 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2)) (word width (rankBase)) (word width (2)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s11.advance.pc = word width (entry + 12)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s11
        (entry + 11) (by rfl) (by omega)
    · rfl
  have live12 : s12.liveWords = state.liveWords + 1 := by
    simp only [s12, State.liveWords, Array.size_push] <;> omega
  have t12 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨12, by decide⟩)]
    have result := copy_add_step s12 2 2 5 (H + 9 + 2 * old) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H + 9 + 2 * old) + (1) = (H + 9 + 2 * old + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 9 + 2 * old + 1))) register
    · rfl
    · rfl
    · rfl
    · change s12.advance.pc = word width (entry + 13)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s12
        (entry + 12) (by rfl) (by omega)
    · rfl
  have live13 : s13.liveWords = state.liveWords + 1 := by
    simp only [s13, State.liveWords, Array.size_push] <;> omega
  have t13 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨13, by decide⟩)]
    have result := copy_branch_nonzero s13 3 (entry + 24) (2) running (by omega) (by omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s13.advance.pc = word width (entry + 14)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s13
        (entry + 13) (by rfl) (by omega)
    · rfl
  have live14 : s14.liveWords = state.liveWords + 1 := by
    simp only [s14, State.liveWords, Array.size_push] <;> omega
  have t14 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 14) (.xor 3 3 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨14, by decide⟩)]
    have result := copy_xor_step s14 3 3 5 (2) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : Nat.xor (2) (1) = (3) := by decide
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (2)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (3))) register
    · rfl
    · rfl
    · rfl
    · change s14.advance.pc = word width (entry + 15)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s14
        (entry + 14) (by rfl) (by omega)
    · rfl
  have live15 : s15.liveWords = state.liveWords + 1 := by
    simp only [s15, State.liveWords, Array.size_push] <;> omega
  have t15 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 15) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨15, by decide⟩)]
    have result := copy_branch_nonzero s15 3 (entry + 24) (3) running (by omega) (by omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s15.advance.pc = word width (entry + 16)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s15
        (entry + 15) (by rfl) (by omega)
    · rfl
  have live16 : s16.liveWords = state.liveWords + 1 := by
    simp only [s16, State.liveWords, Array.size_push] <;> omega
  have t16 : programStep resident s16 = some s17 := by
    rw [fetched resident s16 (entry + 16) (.constant 5 (word width (3))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨16, by decide⟩)]
    have result := copy_constant_step s16 5 (word width (3)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (3)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (3))) register
    · rfl
    · rfl
    · rfl
    · change s16.advance.pc = word width (entry + 17)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s16
        (entry + 16) (by rfl) (by omega)
    · rfl
  have live17 : s17.liveWords = state.liveWords + 1 := by
    simp only [s17, State.liveWords, Array.size_push] <;> omega
  have t17 : programStep resident s17 = some s18 := by
    rw [fetched resident s17 (entry + 17) (.xor 3 3 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨17, by decide⟩)]
    have result := copy_xor_step s17 3 3 5 (3) (3) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : Nat.xor (3) (3) = (0) := by decide
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (3)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1)) (word width (0))) register
    · rfl
    · rfl
    · rfl
    · change s17.advance.pc = word width (entry + 18)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s17
        (entry + 17) (by rfl) (by omega)
    · rfl
  have live18 : s18.liveWords = state.liveWords + 1 := by
    simp only [s18, State.liveWords, Array.size_push] <;> omega
  have t18 : programStep resident s18 = some s19 := by
    rw [fetched resident s18 (entry + 18) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨18, by decide⟩)]
    have result := copy_branch_zero s18 3 (entry + 24) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live19 : s19.liveWords = state.liveWords + 1 := by
    simp only [s19, State.liveWords, Array.size_push] <;> omega
  have t19 : programStep resident s19 = some s20 := by
    rw [fetched resident s19 (entry + 24) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨24, by decide⟩)]
    have result := copy_load_step s19 5 2 (H + 9 + 2 * old + 1) (word width (head)) running (by omega) (by rfl) (by change (state.heap.push (word width 2))[H + 9 + 2 * old + 1]? = some (word width (head)); exact copy_push_cell state.heap _ _ _ headCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1)) (word width (head))) register
    · rfl
    · rfl
    · rfl
    · change s19.advance.pc = word width (entry + 25)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s19
        (entry + 24) (by rfl) (by omega)
    · rfl
  have live20 : s20.liveWords = state.liveWords + 1 := by
    simp only [s20, State.liveWords, Array.size_push] <;> omega
  have t20 : programStep resident s20 = some s21 := by
    rw [fetched resident s20 (entry + 25) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨25, by decide⟩)]
    have result := copy_allocate_step s20 5 (word width (head)) running (by simp only [s20, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s20.advance.pc = word width (entry + 26)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s20
        (entry + 25) (by rfl) (by omega)
    · rfl
  have live21 : s21.liveWords = state.liveWords + 2 := by
    simp only [s21, State.liveWords, Array.size_push] <;> omega
  have t21 : programStep resident s21 = some s22 := by
    rw [fetched resident s21 (entry + 26) (.branchZero 6 (word width (entry + 27))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨26, by decide⟩)]
    have result := copy_branch_zero s21 6 (entry + 27) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live22 : s22.liveWords = state.liveWords + 2 := by
    simp only [s22, State.liveWords, Array.size_push] <;> omega
  have t22 : programStep resident s22 = some s23 := by
    rw [fetched resident s22 (entry + 27) (.constant 3 (word width (1))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨27, by decide⟩)]
    have result := copy_constant_step s22 3 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (0)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s22.advance.pc = word width (entry + 28)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s22
        (entry + 27) (by rfl) (by omega)
    · rfl
  have live23 : s23.liveWords = state.liveWords + 2 := by
    simp only [s23, State.liveWords, Array.size_push] <;> omega
  have t23 : programStep resident s23 = some s24 := by
    rw [fetched resident s23 (entry + 28) (.add 1 1 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨28, by decide⟩)]
    have result := copy_add_step s23 1 1 3 (cursor) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (cursor) + (1) = (cursor + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1)) (word width (cursor + 1))) register
    · rfl
    · rfl
    · rfl
    · change s23.advance.pc = word width (entry + 29)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s23
        (entry + 28) (by rfl) (by omega)
    · rfl
  have live24 : s24.liveWords = state.liveWords + 2 := by
    simp only [s24, State.liveWords, Array.size_push] <;> omega
  have t24 : programStep resident s24 = some s25 := by
    rw [fetched resident s24 (entry + 29) (.add 0 0 7) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨29, by decide⟩)]
    have result := copy_add_step s24 0 0 7 (count) (2 ^ width - 1) running (by omega) (by omega) (by rfl) (by rfl)
    rw [marker_word_decrement count positive countFits] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (count)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1)) (word width (count - 1))) register
    · rfl
    · rfl
    · rfl
    · change s24.advance.pc = word width (entry + 30)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s24
        (entry + 29) (by rfl) (by omega)
    · rfl
  have live25 : s25.liveWords = state.liveWords + 2 := by
    simp only [s25, State.liveWords, Array.size_push] <;> omega
  have t25 : programStep resident s25 = some s26 := by
    rw [fetched resident s25 (entry + 30) (.branchZero 6 (word width (entry))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨30, by decide⟩)]
    have result := copy_branch_zero s25 6 (entry) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live26 : s26.liveWords = state.liveWords + 2 := by
    simp only [s26, State.liveWords, Array.size_push] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.cons t16 (Execution.cons t17 (Execution.cons t18 (Execution.cons t19 (Execution.cons t20 (Execution.cons t21 (Execution.cons t22 (Execution.cons t23 (Execution.cons t24 (Execution.cons t25 (Execution.refl s26))))))))))))))))))))))))))
  refine ⟨s26, max state.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords (max s4.liveWords (max s5.liveWords (max s6.liveWords (max s7.liveWords (max s8.liveWords (max s9.liveWords (max s10.liveWords (max s11.liveWords (max s12.liveWords (max s13.liveWords (max s14.liveWords (max s15.liveWords (max s16.liveWords (max s17.liveWords (max s18.liveWords (max s19.liveWords (max s20.liveWords (max s21.liveWords (max s22.liveWords (max s23.liveWords (max s24.liveWords (max s25.liveWords (s26.liveWords)))))))))))))))))))))))))), ?_, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.reduceAdd] using trace
  · simp only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, live14, live15, live16, live17, live18, live19, live20, live21, live22, live23, live24, live25, live26, max_le_iff]
    omega
  · rfl
  · rfl
  · exact baseHeld.symm
  · exact zeroHeld.symm
  · exact maskHeld.symm

theorem typed_header_case3_execution (resident : Program width 8)
    (nodes base entry done H old head rankBase cursor count : Nat) (mapped : Word width)
    (state : State width 8)
    (physical : ∀ phase : Fin 31, resident[entry + phase.val]? =
      (typedHeaderCopyCode width nodes base entry done)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 31 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width)
    (countFits : count < 2 ^ width) (positive : 0 < count)
    (cursorFits : cursor + 1 < 2 ^ width) (headFits : head < 2 ^ width)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (baseHeld : state.reg 4 = word width rankBase) (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (queueCell : state.heap[cursor]? = some (word width old))
    (tagCell : state.heap[H + 9 + 2 * old]? = some (word width 3))
    (headCell : state.heap[H + 9 + 2 * old + 1]? = some (word width head))
    (rankCell : state.heap[rankBase + head]? = some mapped) :
    ∃ final peak, Execution resident state final 28 peak ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = (state.heap.push (word width 3)).push (mapped) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  let s1 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 7) }
  let s8 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 8) }
  let s9 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 9) }
  let s10 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 10) }
  let s11 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (3)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 11) }
  let s12 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (3)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 12) }
  let s13 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (3)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 13) }
  let s14 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (3)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 14) }
  let s15 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (2)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 15) }
  let s16 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (2)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 16) }
  let s17 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (2)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 17) }
  let s18 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 18) }
  let s19 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 19) }
  let s20 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 20) }
  let s21 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (rankBase + head)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 21) }
  let s22 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (3)), pc := word width (entry + 22) }
  let s23 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (3))).push (mapped), pc := word width (entry + 23) }
  let s24 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (3))).push (mapped), pc := word width (entry + 27) }
  let s25 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (3))).push (mapped), pc := word width (entry + 28) }
  let s26 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (3))).push (mapped), pc := word width (entry + 29) }
  let s27 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (3))).push (mapped), pc := word width (entry + 30) }
  let s28 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (3))).push (mapped), pc := word width (entry + 0) }
  obtain ⟨rawBound, rawValue⟩ := Array.getElem?_eq_some_iff.mp rawCell
  obtain ⟨queueBound, queueValue⟩ := Array.getElem?_eq_some_iff.mp queueCell
  obtain ⟨tagBound, tagValue⟩ := Array.getElem?_eq_some_iff.mp tagCell
  obtain ⟨headBound, headValue⟩ := Array.getElem?_eq_some_iff.mp headCell
  obtain ⟨rankBound, rankValue⟩ := Array.getElem?_eq_some_iff.mp rankCell
  have Hfits : H < 2 ^ width := by omega
  have oldFits : old < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.branchZero 0 (word width (done))) position (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨0, by decide⟩)]
    have result := copy_branch_nonzero state 0 (done) (count) running (by omega) (by omega) (by simp [countHeld, cursorHeld, baseHeld, zeroHeld, maskHeld])
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_initial state count cursor rankBase
        countHeld cursorHeld baseHeld zeroHeld maskHeld) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s1, State.liveWords, Array.size_push] <;> omega
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨1, by decide⟩)]
    have result := copy_constant_step s1 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s2, State.liveWords, Array.size_push] <;> omega
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.load 2 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨2, by decide⟩)]
    have result := copy_load_step s2 2 2 (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base) (word width (H)) running (by omega) (by rfl) (by change state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width (H)); exact rawCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords + 0 := by
    simp only [s3, State.liveWords, Array.size_push] <;> omega
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.load 3 1) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨3, by decide⟩)]
    have result := copy_load_step s3 3 1 (cursor) (word width (old)) running (by omega) (by rfl) (by change state.heap[cursor]? = some (word width (old)); exact queueCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (old))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords + 0 := by
    simp only [s4, State.liveWords, Array.size_push] <;> omega
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.add 3 3 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨4, by decide⟩)]
    have result := copy_add_step s4 3 3 3 (old) (old) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (old) + (old) = (2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords + 0 := by
    simp only [s5, State.liveWords, Array.size_push] <;> omega
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.add 2 2 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨5, by decide⟩)]
    have result := copy_add_step s5 2 2 3 (H) (2 * old) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H) + (2 * old) = (H + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords + 0 := by
    simp only [s6, State.liveWords, Array.size_push] <;> omega
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 5 (word width (9))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨6, by decide⟩)]
    have result := copy_constant_step s6 5 (word width (9)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (9))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords + 0 := by
    simp only [s7, State.liveWords, Array.size_push] <;> omega
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨7, by decide⟩)]
    have result := copy_add_step s7 2 2 5 (H + 2 * old) (9) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H + 2 * old) + (9) = (H + 9 + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 9 + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords + 0 := by
    simp only [s8, State.liveWords, Array.size_push] <;> omega
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨8, by decide⟩)]
    have result := copy_load_step s8 5 2 (H + 9 + 2 * old) (word width (3)) running (by omega) (by rfl) (by change state.heap[H + 9 + 2 * old]? = some (word width (3)); exact tagCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1)) (word width (3))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords + 0 := by
    simp only [s9, State.liveWords, Array.size_push] <;> omega
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨9, by decide⟩)]
    have result := copy_allocate_step s9 5 (word width (3)) running (by simp only [s9, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords + 1 := by
    simp only [s10, State.liveWords, Array.size_push] <;> omega
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.add 3 5 6) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨10, by decide⟩)]
    have result := copy_add_step s10 3 5 6 (3) (0) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (3) + (0) = (3) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1)) (word width (3))) register
    · rfl
    · rfl
    · rfl
    · change s10.advance.pc = word width (entry + 11)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s10
        (entry + 10) (by rfl) (by omega)
    · rfl
  have live11 : s11.liveWords = state.liveWords + 1 := by
    simp only [s11, State.liveWords, Array.size_push] <;> omega
  have t11 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.constant 5 (word width (1))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨11, by decide⟩)]
    have result := copy_constant_step s11 5 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (3)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s11.advance.pc = word width (entry + 12)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s11
        (entry + 11) (by rfl) (by omega)
    · rfl
  have live12 : s12.liveWords = state.liveWords + 1 := by
    simp only [s12, State.liveWords, Array.size_push] <;> omega
  have t12 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨12, by decide⟩)]
    have result := copy_add_step s12 2 2 5 (H + 9 + 2 * old) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H + 9 + 2 * old) + (1) = (H + 9 + 2 * old + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (3)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 9 + 2 * old + 1))) register
    · rfl
    · rfl
    · rfl
    · change s12.advance.pc = word width (entry + 13)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s12
        (entry + 12) (by rfl) (by omega)
    · rfl
  have live13 : s13.liveWords = state.liveWords + 1 := by
    simp only [s13, State.liveWords, Array.size_push] <;> omega
  have t13 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨13, by decide⟩)]
    have result := copy_branch_nonzero s13 3 (entry + 24) (3) running (by omega) (by omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s13.advance.pc = word width (entry + 14)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s13
        (entry + 13) (by rfl) (by omega)
    · rfl
  have live14 : s14.liveWords = state.liveWords + 1 := by
    simp only [s14, State.liveWords, Array.size_push] <;> omega
  have t14 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 14) (.xor 3 3 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨14, by decide⟩)]
    have result := copy_xor_step s14 3 3 5 (3) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : Nat.xor (3) (1) = (2) := by decide
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (3)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (2))) register
    · rfl
    · rfl
    · rfl
    · change s14.advance.pc = word width (entry + 15)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s14
        (entry + 14) (by rfl) (by omega)
    · rfl
  have live15 : s15.liveWords = state.liveWords + 1 := by
    simp only [s15, State.liveWords, Array.size_push] <;> omega
  have t15 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 15) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨15, by decide⟩)]
    have result := copy_branch_nonzero s15 3 (entry + 24) (2) running (by omega) (by omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s15.advance.pc = word width (entry + 16)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s15
        (entry + 15) (by rfl) (by omega)
    · rfl
  have live16 : s16.liveWords = state.liveWords + 1 := by
    simp only [s16, State.liveWords, Array.size_push] <;> omega
  have t16 : programStep resident s16 = some s17 := by
    rw [fetched resident s16 (entry + 16) (.constant 5 (word width (3))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨16, by decide⟩)]
    have result := copy_constant_step s16 5 (word width (3)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (2)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (3))) register
    · rfl
    · rfl
    · rfl
    · change s16.advance.pc = word width (entry + 17)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s16
        (entry + 16) (by rfl) (by omega)
    · rfl
  have live17 : s17.liveWords = state.liveWords + 1 := by
    simp only [s17, State.liveWords, Array.size_push] <;> omega
  have t17 : programStep resident s17 = some s18 := by
    rw [fetched resident s17 (entry + 17) (.xor 3 3 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨17, by decide⟩)]
    have result := copy_xor_step s17 3 3 5 (2) (3) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : Nat.xor (2) (3) = (1) := by decide
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (2)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s17.advance.pc = word width (entry + 18)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s17
        (entry + 17) (by rfl) (by omega)
    · rfl
  have live18 : s18.liveWords = state.liveWords + 1 := by
    simp only [s18, State.liveWords, Array.size_push] <;> omega
  have t18 : programStep resident s18 = some s19 := by
    rw [fetched resident s18 (entry + 18) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨18, by decide⟩)]
    have result := copy_branch_nonzero s18 3 (entry + 24) (1) running (by omega) (by omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s18.advance.pc = word width (entry + 19)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s18
        (entry + 18) (by rfl) (by omega)
    · rfl
  have live19 : s19.liveWords = state.liveWords + 1 := by
    simp only [s19, State.liveWords, Array.size_push] <;> omega
  have t19 : programStep resident s19 = some s20 := by
    rw [fetched resident s19 (entry + 19) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨19, by decide⟩)]
    have result := copy_load_step s19 5 2 (H + 9 + 2 * old + 1) (word width (head)) running (by omega) (by rfl) (by change (state.heap.push (word width 3))[H + 9 + 2 * old + 1]? = some (word width (head)); exact copy_push_cell state.heap _ _ _ headCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1)) (word width (head))) register
    · rfl
    · rfl
    · rfl
    · change s19.advance.pc = word width (entry + 20)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s19
        (entry + 19) (by rfl) (by omega)
    · rfl
  have live20 : s20.liveWords = state.liveWords + 1 := by
    simp only [s20, State.liveWords, Array.size_push] <;> omega
  have t20 : programStep resident s20 = some s21 := by
    rw [fetched resident s20 (entry + 20) (.add 5 5 4) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨20, by decide⟩)]
    have result := copy_add_step s20 5 5 4 (head) (rankBase) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (head) + (rankBase) = (rankBase + head) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1)) (word width (rankBase + head))) register
    · rfl
    · rfl
    · rfl
    · change s20.advance.pc = word width (entry + 21)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s20
        (entry + 20) (by rfl) (by omega)
    · rfl
  have live21 : s21.liveWords = state.liveWords + 1 := by
    simp only [s21, State.liveWords, Array.size_push] <;> omega
  have t21 : programStep resident s21 = some s22 := by
    rw [fetched resident s21 (entry + 21) (.load 5 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨21, by decide⟩)]
    have result := copy_load_step s21 5 5 (rankBase + head) (mapped) running (by omega) (by rfl) (by change (state.heap.push (word width 3))[rankBase + head]? = some (mapped); exact copy_push_cell state.heap _ _ _ rankCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (word width (rankBase + head)) (word width (0)) (word width (2 ^ width - 1)) (mapped)) register
    · rfl
    · rfl
    · rfl
    · change s21.advance.pc = word width (entry + 22)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s21
        (entry + 21) (by rfl) (by omega)
    · rfl
  have live22 : s22.liveWords = state.liveWords + 1 := by
    simp only [s22, State.liveWords, Array.size_push] <;> omega
  have t22 : programStep resident s22 = some s23 := by
    rw [fetched resident s22 (entry + 22) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨22, by decide⟩)]
    have result := copy_allocate_step s22 5 (mapped) running (by simp only [s22, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s22.advance.pc = word width (entry + 23)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s22
        (entry + 22) (by rfl) (by omega)
    · rfl
  have live23 : s23.liveWords = state.liveWords + 2 := by
    simp only [s23, State.liveWords, Array.size_push] <;> omega
  have t23 : programStep resident s23 = some s24 := by
    rw [fetched resident s23 (entry + 23) (.branchZero 6 (word width (entry + 27))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨23, by decide⟩)]
    have result := copy_branch_zero s23 6 (entry + 27) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live24 : s24.liveWords = state.liveWords + 2 := by
    simp only [s24, State.liveWords, Array.size_push] <;> omega
  have t24 : programStep resident s24 = some s25 := by
    rw [fetched resident s24 (entry + 27) (.constant 3 (word width (1))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨27, by decide⟩)]
    have result := copy_constant_step s24 3 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s24.advance.pc = word width (entry + 28)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s24
        (entry + 27) (by rfl) (by omega)
    · rfl
  have live25 : s25.liveWords = state.liveWords + 2 := by
    simp only [s25, State.liveWords, Array.size_push] <;> omega
  have t25 : programStep resident s25 = some s26 := by
    rw [fetched resident s25 (entry + 28) (.add 1 1 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨28, by decide⟩)]
    have result := copy_add_step s25 1 1 3 (cursor) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (cursor) + (1) = (cursor + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1)) (word width (cursor + 1))) register
    · rfl
    · rfl
    · rfl
    · change s25.advance.pc = word width (entry + 29)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s25
        (entry + 28) (by rfl) (by omega)
    · rfl
  have live26 : s26.liveWords = state.liveWords + 2 := by
    simp only [s26, State.liveWords, Array.size_push] <;> omega
  have t26 : programStep resident s26 = some s27 := by
    rw [fetched resident s26 (entry + 29) (.add 0 0 7) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨29, by decide⟩)]
    have result := copy_add_step s26 0 0 7 (count) (2 ^ width - 1) running (by omega) (by omega) (by rfl) (by rfl)
    rw [marker_word_decrement count positive countFits] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (count)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1)) (word width (count - 1))) register
    · rfl
    · rfl
    · rfl
    · change s26.advance.pc = word width (entry + 30)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s26
        (entry + 29) (by rfl) (by omega)
    · rfl
  have live27 : s27.liveWords = state.liveWords + 2 := by
    simp only [s27, State.liveWords, Array.size_push] <;> omega
  have t27 : programStep resident s27 = some s28 := by
    rw [fetched resident s27 (entry + 30) (.branchZero 6 (word width (entry))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨30, by decide⟩)]
    have result := copy_branch_zero s27 6 (entry) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live28 : s28.liveWords = state.liveWords + 2 := by
    simp only [s28, State.liveWords, Array.size_push] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.cons t16 (Execution.cons t17 (Execution.cons t18 (Execution.cons t19 (Execution.cons t20 (Execution.cons t21 (Execution.cons t22 (Execution.cons t23 (Execution.cons t24 (Execution.cons t25 (Execution.cons t26 (Execution.cons t27 (Execution.refl s28))))))))))))))))))))))))))))
  refine ⟨s28, max state.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords (max s4.liveWords (max s5.liveWords (max s6.liveWords (max s7.liveWords (max s8.liveWords (max s9.liveWords (max s10.liveWords (max s11.liveWords (max s12.liveWords (max s13.liveWords (max s14.liveWords (max s15.liveWords (max s16.liveWords (max s17.liveWords (max s18.liveWords (max s19.liveWords (max s20.liveWords (max s21.liveWords (max s22.liveWords (max s23.liveWords (max s24.liveWords (max s25.liveWords (max s26.liveWords (max s27.liveWords (s28.liveWords)))))))))))))))))))))))))))), ?_, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.reduceAdd] using trace
  · simp only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, live14, live15, live16, live17, live18, live19, live20, live21, live22, live23, live24, live25, live26, live27, live28, max_le_iff]
    omega
  · rfl
  · rfl
  · exact baseHeld.symm
  · exact zeroHeld.symm
  · exact maskHeld.symm

theorem typed_header_case4_execution (resident : Program width 8)
    (nodes base entry done H old head rankBase cursor count : Nat) (mapped : Word width)
    (state : State width 8)
    (physical : ∀ phase : Fin 31, resident[entry + phase.val]? =
      (typedHeaderCopyCode width nodes base entry done)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 31 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width)
    (countFits : count < 2 ^ width) (positive : 0 < count)
    (cursorFits : cursor + 1 < 2 ^ width) (headFits : head < 2 ^ width)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (baseHeld : state.reg 4 = word width rankBase) (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (queueCell : state.heap[cursor]? = some (word width old))
    (tagCell : state.heap[H + 9 + 2 * old]? = some (word width 4))
    (headCell : state.heap[H + 9 + 2 * old + 1]? = some (word width head))
    (rankCell : state.heap[rankBase + head]? = some mapped) :
    ∃ final peak, Execution resident state final 28 peak ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = (state.heap.push (word width 4)).push (mapped) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  let s1 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 7) }
  let s8 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 8) }
  let s9 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (4)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 9) }
  let s10 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (4)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 10) }
  let s11 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (4)) (word width (rankBase)) (word width (4)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 11) }
  let s12 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (4)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 12) }
  let s13 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (4)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 13) }
  let s14 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (4)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 14) }
  let s15 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (5)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 15) }
  let s16 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (5)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 16) }
  let s17 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (5)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 17) }
  let s18 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (6)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 18) }
  let s19 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (6)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 19) }
  let s20 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (6)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 20) }
  let s21 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (6)) (word width (rankBase)) (word width (rankBase + head)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 21) }
  let s22 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (6)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (4)), pc := word width (entry + 22) }
  let s23 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (6)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (4))).push (mapped), pc := word width (entry + 23) }
  let s24 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (6)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (4))).push (mapped), pc := word width (entry + 27) }
  let s25 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (4))).push (mapped), pc := word width (entry + 28) }
  let s26 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (4))).push (mapped), pc := word width (entry + 29) }
  let s27 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (4))).push (mapped), pc := word width (entry + 30) }
  let s28 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (4))).push (mapped), pc := word width (entry + 0) }
  obtain ⟨rawBound, rawValue⟩ := Array.getElem?_eq_some_iff.mp rawCell
  obtain ⟨queueBound, queueValue⟩ := Array.getElem?_eq_some_iff.mp queueCell
  obtain ⟨tagBound, tagValue⟩ := Array.getElem?_eq_some_iff.mp tagCell
  obtain ⟨headBound, headValue⟩ := Array.getElem?_eq_some_iff.mp headCell
  obtain ⟨rankBound, rankValue⟩ := Array.getElem?_eq_some_iff.mp rankCell
  have Hfits : H < 2 ^ width := by omega
  have oldFits : old < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.branchZero 0 (word width (done))) position (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨0, by decide⟩)]
    have result := copy_branch_nonzero state 0 (done) (count) running (by omega) (by omega) (by simp [countHeld, cursorHeld, baseHeld, zeroHeld, maskHeld])
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_initial state count cursor rankBase
        countHeld cursorHeld baseHeld zeroHeld maskHeld) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s1, State.liveWords, Array.size_push] <;> omega
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨1, by decide⟩)]
    have result := copy_constant_step s1 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s2, State.liveWords, Array.size_push] <;> omega
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.load 2 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨2, by decide⟩)]
    have result := copy_load_step s2 2 2 (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base) (word width (H)) running (by omega) (by rfl) (by change state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width (H)); exact rawCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords + 0 := by
    simp only [s3, State.liveWords, Array.size_push] <;> omega
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.load 3 1) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨3, by decide⟩)]
    have result := copy_load_step s3 3 1 (cursor) (word width (old)) running (by omega) (by rfl) (by change state.heap[cursor]? = some (word width (old)); exact queueCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (old))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords + 0 := by
    simp only [s4, State.liveWords, Array.size_push] <;> omega
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.add 3 3 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨4, by decide⟩)]
    have result := copy_add_step s4 3 3 3 (old) (old) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (old) + (old) = (2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords + 0 := by
    simp only [s5, State.liveWords, Array.size_push] <;> omega
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.add 2 2 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨5, by decide⟩)]
    have result := copy_add_step s5 2 2 3 (H) (2 * old) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H) + (2 * old) = (H + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords + 0 := by
    simp only [s6, State.liveWords, Array.size_push] <;> omega
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 5 (word width (9))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨6, by decide⟩)]
    have result := copy_constant_step s6 5 (word width (9)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (9))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords + 0 := by
    simp only [s7, State.liveWords, Array.size_push] <;> omega
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨7, by decide⟩)]
    have result := copy_add_step s7 2 2 5 (H + 2 * old) (9) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H + 2 * old) + (9) = (H + 9 + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 9 + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords + 0 := by
    simp only [s8, State.liveWords, Array.size_push] <;> omega
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨8, by decide⟩)]
    have result := copy_load_step s8 5 2 (H + 9 + 2 * old) (word width (4)) running (by omega) (by rfl) (by change state.heap[H + 9 + 2 * old]? = some (word width (4)); exact tagCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (9)) (word width (0)) (word width (2 ^ width - 1)) (word width (4))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords + 0 := by
    simp only [s9, State.liveWords, Array.size_push] <;> omega
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨9, by decide⟩)]
    have result := copy_allocate_step s9 5 (word width (4)) running (by simp only [s9, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords + 1 := by
    simp only [s10, State.liveWords, Array.size_push] <;> omega
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.add 3 5 6) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨10, by decide⟩)]
    have result := copy_add_step s10 3 5 6 (4) (0) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (4) + (0) = (4) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (2 * old)) (word width (rankBase)) (word width (4)) (word width (0)) (word width (2 ^ width - 1)) (word width (4))) register
    · rfl
    · rfl
    · rfl
    · change s10.advance.pc = word width (entry + 11)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s10
        (entry + 10) (by rfl) (by omega)
    · rfl
  have live11 : s11.liveWords = state.liveWords + 1 := by
    simp only [s11, State.liveWords, Array.size_push] <;> omega
  have t11 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.constant 5 (word width (1))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨11, by decide⟩)]
    have result := copy_constant_step s11 5 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (4)) (word width (rankBase)) (word width (4)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s11.advance.pc = word width (entry + 12)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s11
        (entry + 11) (by rfl) (by omega)
    · rfl
  have live12 : s12.liveWords = state.liveWords + 1 := by
    simp only [s12, State.liveWords, Array.size_push] <;> omega
  have t12 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨12, by decide⟩)]
    have result := copy_add_step s12 2 2 5 (H + 9 + 2 * old) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H + 9 + 2 * old) + (1) = (H + 9 + 2 * old + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old)) (word width (4)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 9 + 2 * old + 1))) register
    · rfl
    · rfl
    · rfl
    · change s12.advance.pc = word width (entry + 13)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s12
        (entry + 12) (by rfl) (by omega)
    · rfl
  have live13 : s13.liveWords = state.liveWords + 1 := by
    simp only [s13, State.liveWords, Array.size_push] <;> omega
  have t13 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨13, by decide⟩)]
    have result := copy_branch_nonzero s13 3 (entry + 24) (4) running (by omega) (by omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s13.advance.pc = word width (entry + 14)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s13
        (entry + 13) (by rfl) (by omega)
    · rfl
  have live14 : s14.liveWords = state.liveWords + 1 := by
    simp only [s14, State.liveWords, Array.size_push] <;> omega
  have t14 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 14) (.xor 3 3 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨14, by decide⟩)]
    have result := copy_xor_step s14 3 3 5 (4) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : Nat.xor (4) (1) = (5) := by decide
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (4)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (5))) register
    · rfl
    · rfl
    · rfl
    · change s14.advance.pc = word width (entry + 15)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s14
        (entry + 14) (by rfl) (by omega)
    · rfl
  have live15 : s15.liveWords = state.liveWords + 1 := by
    simp only [s15, State.liveWords, Array.size_push] <;> omega
  have t15 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 15) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨15, by decide⟩)]
    have result := copy_branch_nonzero s15 3 (entry + 24) (5) running (by omega) (by omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s15.advance.pc = word width (entry + 16)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s15
        (entry + 15) (by rfl) (by omega)
    · rfl
  have live16 : s16.liveWords = state.liveWords + 1 := by
    simp only [s16, State.liveWords, Array.size_push] <;> omega
  have t16 : programStep resident s16 = some s17 := by
    rw [fetched resident s16 (entry + 16) (.constant 5 (word width (3))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨16, by decide⟩)]
    have result := copy_constant_step s16 5 (word width (3)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (5)) (word width (rankBase)) (word width (1)) (word width (0)) (word width (2 ^ width - 1)) (word width (3))) register
    · rfl
    · rfl
    · rfl
    · change s16.advance.pc = word width (entry + 17)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s16
        (entry + 16) (by rfl) (by omega)
    · rfl
  have live17 : s17.liveWords = state.liveWords + 1 := by
    simp only [s17, State.liveWords, Array.size_push] <;> omega
  have t17 : programStep resident s17 = some s18 := by
    rw [fetched resident s17 (entry + 17) (.xor 3 3 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨17, by decide⟩)]
    have result := copy_xor_step s17 3 3 5 (5) (3) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : Nat.xor (5) (3) = (6) := by decide
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (5)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1)) (word width (6))) register
    · rfl
    · rfl
    · rfl
    · change s17.advance.pc = word width (entry + 18)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s17
        (entry + 17) (by rfl) (by omega)
    · rfl
  have live18 : s18.liveWords = state.liveWords + 1 := by
    simp only [s18, State.liveWords, Array.size_push] <;> omega
  have t18 : programStep resident s18 = some s19 := by
    rw [fetched resident s18 (entry + 18) (.branchZero 3 (word width (entry + 24))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨18, by decide⟩)]
    have result := copy_branch_nonzero s18 3 (entry + 24) (6) running (by omega) (by omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s18.advance.pc = word width (entry + 19)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s18
        (entry + 18) (by rfl) (by omega)
    · rfl
  have live19 : s19.liveWords = state.liveWords + 1 := by
    simp only [s19, State.liveWords, Array.size_push] <;> omega
  have t19 : programStep resident s19 = some s20 := by
    rw [fetched resident s19 (entry + 19) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨19, by decide⟩)]
    have result := copy_load_step s19 5 2 (H + 9 + 2 * old + 1) (word width (head)) running (by omega) (by rfl) (by change (state.heap.push (word width 4))[H + 9 + 2 * old + 1]? = some (word width (head)); exact copy_push_cell state.heap _ _ _ headCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (6)) (word width (rankBase)) (word width (3)) (word width (0)) (word width (2 ^ width - 1)) (word width (head))) register
    · rfl
    · rfl
    · rfl
    · change s19.advance.pc = word width (entry + 20)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s19
        (entry + 19) (by rfl) (by omega)
    · rfl
  have live20 : s20.liveWords = state.liveWords + 1 := by
    simp only [s20, State.liveWords, Array.size_push] <;> omega
  have t20 : programStep resident s20 = some s21 := by
    rw [fetched resident s20 (entry + 20) (.add 5 5 4) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨20, by decide⟩)]
    have result := copy_add_step s20 5 5 4 (head) (rankBase) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (head) + (rankBase) = (rankBase + head) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (6)) (word width (rankBase)) (word width (head)) (word width (0)) (word width (2 ^ width - 1)) (word width (rankBase + head))) register
    · rfl
    · rfl
    · rfl
    · change s20.advance.pc = word width (entry + 21)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s20
        (entry + 20) (by rfl) (by omega)
    · rfl
  have live21 : s21.liveWords = state.liveWords + 1 := by
    simp only [s21, State.liveWords, Array.size_push] <;> omega
  have t21 : programStep resident s21 = some s22 := by
    rw [fetched resident s21 (entry + 21) (.load 5 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨21, by decide⟩)]
    have result := copy_load_step s21 5 5 (rankBase + head) (mapped) running (by omega) (by rfl) (by change (state.heap.push (word width 4))[rankBase + head]? = some (mapped); exact copy_push_cell state.heap _ _ _ rankCell)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (6)) (word width (rankBase)) (word width (rankBase + head)) (word width (0)) (word width (2 ^ width - 1)) (mapped)) register
    · rfl
    · rfl
    · rfl
    · change s21.advance.pc = word width (entry + 22)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s21
        (entry + 21) (by rfl) (by omega)
    · rfl
  have live22 : s22.liveWords = state.liveWords + 1 := by
    simp only [s22, State.liveWords, Array.size_push] <;> omega
  have t22 : programStep resident s22 = some s23 := by
    rw [fetched resident s22 (entry + 22) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨22, by decide⟩)]
    have result := copy_allocate_step s22 5 (mapped) running (by simp only [s22, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s22.advance.pc = word width (entry + 23)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s22
        (entry + 22) (by rfl) (by omega)
    · rfl
  have live23 : s23.liveWords = state.liveWords + 2 := by
    simp only [s23, State.liveWords, Array.size_push] <;> omega
  have t23 : programStep resident s23 = some s24 := by
    rw [fetched resident s23 (entry + 23) (.branchZero 6 (word width (entry + 27))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨23, by decide⟩)]
    have result := copy_branch_zero s23 6 (entry + 27) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live24 : s24.liveWords = state.liveWords + 2 := by
    simp only [s24, State.liveWords, Array.size_push] <;> omega
  have t24 : programStep resident s24 = some s25 := by
    rw [fetched resident s24 (entry + 27) (.constant 3 (word width (1))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨27, by decide⟩)]
    have result := copy_constant_step s24 3 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (6)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s24.advance.pc = word width (entry + 28)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s24
        (entry + 27) (by rfl) (by omega)
    · rfl
  have live25 : s25.liveWords = state.liveWords + 2 := by
    simp only [s25, State.liveWords, Array.size_push] <;> omega
  have t25 : programStep resident s25 = some s26 := by
    rw [fetched resident s25 (entry + 28) (.add 1 1 3) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨28, by decide⟩)]
    have result := copy_add_step s25 1 1 3 (cursor) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (cursor) + (1) = (cursor + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (count)) (word width (cursor)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1)) (word width (cursor + 1))) register
    · rfl
    · rfl
    · rfl
    · change s25.advance.pc = word width (entry + 29)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s25
        (entry + 28) (by rfl) (by omega)
    · rfl
  have live26 : s26.liveWords = state.liveWords + 2 := by
    simp only [s26, State.liveWords, Array.size_push] <;> omega
  have t26 : programStep resident s26 = some s27 := by
    rw [fetched resident s26 (entry + 29) (.add 0 0 7) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨29, by decide⟩)]
    have result := copy_add_step s26 0 0 7 (count) (2 ^ width - 1) running (by omega) (by omega) (by rfl) (by rfl)
    rw [marker_word_decrement count positive countFits] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (count)) (word width (cursor + 1)) (word width (H + 9 + 2 * old + 1)) (word width (1)) (word width (rankBase)) (mapped) (word width (0)) (word width (2 ^ width - 1)) (word width (count - 1))) register
    · rfl
    · rfl
    · rfl
    · change s26.advance.pc = word width (entry + 30)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s26
        (entry + 29) (by rfl) (by omega)
    · rfl
  have live27 : s27.liveWords = state.liveWords + 2 := by
    simp only [s27, State.liveWords, Array.size_push] <;> omega
  have t27 : programStep resident s27 = some s28 := by
    rw [fetched resident s27 (entry + 30) (.branchZero 6 (word width (entry))) (by rfl) (by omega)
      (by simpa [typedHeaderCopyCode] using physical ⟨30, by decide⟩)]
    have result := copy_branch_zero s27 6 (entry) running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live28 : s28.liveWords = state.liveWords + 2 := by
    simp only [s28, State.liveWords, Array.size_push] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.cons t16 (Execution.cons t17 (Execution.cons t18 (Execution.cons t19 (Execution.cons t20 (Execution.cons t21 (Execution.cons t22 (Execution.cons t23 (Execution.cons t24 (Execution.cons t25 (Execution.cons t26 (Execution.cons t27 (Execution.refl s28))))))))))))))))))))))))))))
  refine ⟨s28, max state.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords (max s4.liveWords (max s5.liveWords (max s6.liveWords (max s7.liveWords (max s8.liveWords (max s9.liveWords (max s10.liveWords (max s11.liveWords (max s12.liveWords (max s13.liveWords (max s14.liveWords (max s15.liveWords (max s16.liveWords (max s17.liveWords (max s18.liveWords (max s19.liveWords (max s20.liveWords (max s21.liveWords (max s22.liveWords (max s23.liveWords (max s24.liveWords (max s25.liveWords (max s26.liveWords (max s27.liveWords (s28.liveWords)))))))))))))))))))))))))))), ?_, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.reduceAdd] using trace
  · simp only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, live14, live15, live16, live17, live18, live19, live20, live21, live22, live23, live24, live25, live26, live27, live28, max_le_iff]
    omega
  · rfl
  · rfl
  · exact baseHeld.symm
  · exact zeroHeld.symm
  · exact maskHeld.symm

-- Private full typed-copy prefix: dynamically record its actual allocation
-- origin in dead nextSlot without losing the rank base in r4 or raw base in
-- activeSlot. Source global words are [V,n,R,E,U,...]; typed words [n,V,E,U,R].
def typedGlobalCopyCode (width nodes base headerEntry : Nat) : Program width 8 :=
  #[.constant 3 (word width nodes),
    .add 3 4 3,
    .constant 2 (word width (Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base)),
    .store 2 3,
    .constant 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)),
    .load 2 2,
    .constant 3 (word width 1), .add 5 2 3, .load 5 5, .allocate 5,
    .constant 3 (word width 0), .add 5 2 3, .load 5 5, .allocate 5,
    .constant 3 (word width 3), .add 5 2 3, .load 5 5, .allocate 5,
    .constant 3 (word width 4), .add 5 2 3, .load 5 5, .allocate 5,
    .constant 3 (word width 2), .add 5 2 3, .load 5 5, .allocate 5,
    .constant 0 (word width nodes),
    .constant 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)),
    .constant 6 (word width 0),
    .constant 7 (word width (2 ^ width - 1)),
    .branchZero 6 (word width headerEntry)]

-- 31 actual fetched instructions, allocates5 metadata words, peakinitial+5.
-- Derived actual origin is r4+V=rankBase+V=heap.size before the5 allocations.
-- nextSlot<queueStart and below runtime raw/rank regions; its one store preserves
-- the produced Q, raw packet, rank table, and saved raw base at activeSlot.
-- Result r4 rankBase survives, r0=V,r1=Qstart,r6zero,r7mask; header loop consumes
-- the exact row headers and rank table. Final transfer recovers typed origin
-- with two fetched constant/load instructions at nextSlot, rather than a free
-- heap-size query or immediate depending on runtime deduplicated incidence P.

def typedDirectorySetupCode (width nodes children base entry : Nat) : Program width 8 :=
  #[.constant 5 (word width (5 + 6 * nodes)),
    .constant 2 (word width (Controller.Horn.WorklistFIFO.headSlot (n := nodes) base)), .store 2 5,
    .constant 5 (word width (5 + 6 * nodes + children)),
    .constant 2 (word width (Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base)), .store 2 5,
    .constant 0 (word width nodes),
    .constant 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)),
    .constant 6 (word width 0), .constant 7 (word width (2 ^ width - 1)),
    .branchZero 6 (word width entry)]

def typedDirectoryCopyCode (width nodes base entry done : Nat) : Program width 8 :=
  #[.branchZero 0 (word width done),
    .constant 2 (word width (Controller.Horn.WorklistFIFO.headSlot (n := nodes) base)), .load 5 2, .allocate 5,
    .constant 2 (word width (Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base)), .load 5 2, .allocate 5,
    .constant 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)), .load 2 2,
    .load 3 1, .add 3 3 3, .add 2 2 3,
    .constant 5 (word width (9 + 4 * nodes)), .add 2 2 5, .load 5 2,
    .constant 3 (word width (Controller.Horn.WorklistFIFO.headSlot (n := nodes) base)), .load 3 3,
    .add 5 5 3,
    .constant 3 (word width (Controller.Horn.WorklistFIFO.headSlot (n := nodes) base)), .store 3 5,
    .constant 3 (word width 1), .add 2 2 3, .load 5 2,
    .constant 3 (word width (Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base)), .load 3 3,
    .add 5 5 3,
    .constant 3 (word width (Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base)), .store 3 5,
    .constant 3 (word width 1), .add 1 1 3, .add 0 0 7, .branchZero 6 (word width entry)]

-- Initial relative child/guard cursors are5+6V and5+6V+E. Each iteration
-- emits current cursor pair, reads selected original row's actual arities,
-- then stores updated relative cursors into dead headSlot/tailSlot.
-- The directories therefore match rowBases of the actual Q-selected rows,
-- with one prefix increment per original represented incidence (no rescan).
-- All stores are below Q and distinct from rawBase activeSlot / typedBase nextSlot.
-- Actual32V+1 loop ticks, alloc2V; setup11 ticks. Directory addresses are relative
-- to final cold packet origin0, not the temporary allocation base in shared heap.

/-- Stored source tag/head and its actual rank lookup select the fetched branch.
The trace performs two allocations and returns to the same loop entry. -/
theorem header_row_execution (resident : Program width 8)
    (nodes base entry done H old head rankBase cursor count : Nat) (mapped : Word width)
    (tag : Fin 5) (state : State width 8)
    (physical : ∀ phase : Fin 31, resident[entry + phase.val]? =
      (typedHeaderCopyCode width nodes base entry done)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 31 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width)
    (countFits : count < 2 ^ width) (positive : 0 < count)
    (cursorFits : cursor + 1 < 2 ^ width) (headFits : head < 2 ^ width)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (baseHeld : state.reg 4 = word width rankBase) (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (queueCell : state.heap[cursor]? = some (word width old))
    (tagCell : state.heap[H + 9 + 2 * old]? = some (word width tag.val))
    (headCell : state.heap[H + 9 + 2 * old + 1]? = some (word width head))
    (rankCell : 3 ≤ tag.val → state.heap[rankBase + head]? = some mapped) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧ ticks ≤ 28 ∧
      peak ≤ state.liveWords + 2 ∧
      final.heap = (state.heap.push (word width tag.val)).push
        (if tag.val < 3 then word width head else mapped) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  have alternatives : tag.val = 0 ∨ tag.val = 1 ∨ tag.val = 2 ∨ tag.val = 3 ∨ tag.val = 4 := by
    have := tag.isLt
    omega
  rcases alternatives with selected | selected | selected | selected | selected
  · have actualTag : state.heap[H + 9 + 2 * old]? = some (word width 0) := by
      simpa only [selected] using tagCell
    obtain ⟨final, peak, trace, space, heap, stack, output, pc, halted, countReg,
      cursorReg, rankReg, zeroReg, maskReg⟩ := typed_header_case0_execution resident
        nodes base entry done H old head rankBase cursor count mapped state physical
        position running codeFits room countFits positive cursorFits headFits
        countHeld cursorHeld baseHeld zeroHeld maskHeld rawCell queueCell actualTag headCell
    refine ⟨final, 21, peak, trace, by decide, space, ?_, stack, output, pc, halted,
      countReg, cursorReg, rankReg, zeroReg, maskReg⟩
    simpa only [selected, Nat.reduceLT, ite_true, ite_false] using heap
  · have actualTag : state.heap[H + 9 + 2 * old]? = some (word width 1) := by
      simpa only [selected] using tagCell
    obtain ⟨final, peak, trace, space, heap, stack, output, pc, halted, countReg,
      cursorReg, rankReg, zeroReg, maskReg⟩ := typed_header_case1_execution resident
        nodes base entry done H old head rankBase cursor count mapped state physical
        position running codeFits room countFits positive cursorFits headFits
        countHeld cursorHeld baseHeld zeroHeld maskHeld rawCell queueCell actualTag headCell
    refine ⟨final, 23, peak, trace, by decide, space, ?_, stack, output, pc, halted,
      countReg, cursorReg, rankReg, zeroReg, maskReg⟩
    simpa only [selected, Nat.reduceLT, ite_true, ite_false] using heap
  · have actualTag : state.heap[H + 9 + 2 * old]? = some (word width 2) := by
      simpa only [selected] using tagCell
    obtain ⟨final, peak, trace, space, heap, stack, output, pc, halted, countReg,
      cursorReg, rankReg, zeroReg, maskReg⟩ := typed_header_case2_execution resident
        nodes base entry done H old head rankBase cursor count mapped state physical
        position running codeFits room countFits positive cursorFits headFits
        countHeld cursorHeld baseHeld zeroHeld maskHeld rawCell queueCell actualTag headCell
    refine ⟨final, 26, peak, trace, by decide, space, ?_, stack, output, pc, halted,
      countReg, cursorReg, rankReg, zeroReg, maskReg⟩
    simpa only [selected, Nat.reduceLT, ite_true, ite_false] using heap
  · have actualTag : state.heap[H + 9 + 2 * old]? = some (word width 3) := by
      simpa only [selected] using tagCell
    obtain ⟨final, peak, trace, space, heap, stack, output, pc, halted, countReg,
      cursorReg, rankReg, zeroReg, maskReg⟩ := typed_header_case3_execution resident
        nodes base entry done H old head rankBase cursor count mapped state physical
        position running codeFits room countFits positive cursorFits headFits
        countHeld cursorHeld baseHeld zeroHeld maskHeld rawCell queueCell actualTag headCell (rankCell (by omega))
    refine ⟨final, 28, peak, trace, by decide, space, ?_, stack, output, pc, halted,
      countReg, cursorReg, rankReg, zeroReg, maskReg⟩
    simpa only [selected, Nat.reduceLT, ite_true, ite_false] using heap
  · have actualTag : state.heap[H + 9 + 2 * old]? = some (word width 4) := by
      simpa only [selected] using tagCell
    obtain ⟨final, peak, trace, space, heap, stack, output, pc, halted, countReg,
      cursorReg, rankReg, zeroReg, maskReg⟩ := typed_header_case4_execution resident
        nodes base entry done H old head rankBase cursor count mapped state physical
        position running codeFits room countFits positive cursorFits headFits
        countHeld cursorHeld baseHeld zeroHeld maskHeld rawCell queueCell actualTag headCell (rankCell (by omega))
    refine ⟨final, 28, peak, trace, by decide, space, ?_, stack, output, pc, halted,
      countReg, cursorReg, rankReg, zeroReg, maskReg⟩
    simpa only [selected, Nat.reduceLT, ite_true, ite_false] using heap

theorem copy_pair_array (heap : Array (Word width)) (first second : Word width)
    (rest : List (Word width)) :
    (heap.push first).push second ++ rest.toArray = heap ++ (first :: second :: rest).toArray := by
  have conversion : (first :: second :: rest).toArray =
      #[first] ++ (#[second] ++ rest.toArray) :=
    (List.toArray_cons first (second :: rest)).trans
      (congrArg (fun tail : Array (Word width) => #[first] ++ tail)
        (List.toArray_cons second rest))
  change ((heap ++ #[first]) ++ #[second]) ++ rest.toArray = _
  rw [conversion]
  simp only [Array.append_assoc]

theorem copy_nil_array {α : Type} : ([] : List α).toArray = #[] := rfl

/-- One original stored row, selected by its produced FIFO identifier. -/
structure HeaderSourceRow (width : Nat) where
  old : Nat
  tag : Fin 5
  head : Nat
  mapped : Word width

def HeaderSourceRow.resultHead (row : HeaderSourceRow width) : Word width :=
  if row.tag.val < 3 then word width row.head else row.mapped

def copiedHeaderWords (rows : List (HeaderSourceRow width)) : List (Word width) :=
  rows.flatMap fun row => [word width row.tag.val, row.resultHead]

/-- Every source premise is an actual heap cell, including the produced queue
and the rank-table load required by guard and live-AND rows. -/
def HeaderRowsStored (heap : Array (Word width)) (H cursor rankBase : Nat)
    (rows : List (HeaderSourceRow width)) : Prop :=
  ∀ index : Fin rows.length,
    let row := rows[index.val]
    heap[cursor + index.val]? = some (word width row.old) ∧
    heap[H + 9 + 2 * row.old]? = some (word width row.tag.val) ∧
    heap[H + 9 + 2 * row.old + 1]? = some (word width row.head) ∧
    (3 ≤ row.tag.val → heap[rankBase + row.head]? = some row.mapped) ∧
    row.head < 2 ^ width

theorem copied_pair_preserves (heap : Array (Word width)) (first second value : Word width)
    (address : Nat) (cell : heap[address]? = some value) :
    ((heap.push first).push second)[address]? = some value := by
  obtain ⟨valid, actual⟩ := Array.getElem?_eq_some_iff.mp cell
  rw [Array.getElem?_eq_getElem (by simp only [Array.size_push]; omega)]
  rw [Array.getElem_push_lt (by simp only [Array.size_push]; omega),
    Array.getElem_push_lt valid, actual]

/-- The complete fetched header loop traverses the produced FIFO order once.
Its allocation is exactly two words per selected original row; source, queue
and rank cells remain available at their original addresses. -/
theorem header_loop_execution (resident : Program width 8)
    (nodes base entry done H rankBase : Nat)
    (physical : ∀ phase : Fin 31, resident[entry + phase.val]? =
      (typedHeaderCopyCode width nodes base entry done)[phase.val]?)
    (codeFits : entry + 31 < 2 ^ width) :
    ∀ (rows : List (HeaderSourceRow width)) (cursor : Nat) (state : State width 8),
    state.pc = word width entry → state.halted = false →
    state.heap.size + 2 * rows.length < 2 ^ width →
    cursor + rows.length < 2 ^ width → rows.length < 2 ^ width →
    state.reg 0 = word width rows.length → state.reg 1 = word width cursor →
    state.reg 4 = word width rankBase → state.reg 6 = word width 0 →
    state.reg 7 = word width (2 ^ width - 1) →
    state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H) →
    HeaderRowsStored state.heap H cursor rankBase rows →
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 28 * rows.length + 1 ∧ peak ≤ state.liveWords + 2 * rows.length ∧
      final.heap = state.heap ++ (copiedHeaderWords rows).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width (cursor + rows.length) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  intro rows
  induction rows with
  | nil =>
    intro cursor state position running room cursorFits countFits countHeld cursorHeld
      rankHeld zeroHeld maskHeld rawCell stored
    let final : State width 8 := { state.advance with pc := word width done }
    have transition : programStep resident state = some final := by
      rw [fetched resident state entry (.branchZero 0 (word width done)) position (by omega)
        (by simpa [typedHeaderCopyCode] using physical ⟨0, by decide⟩)]
      exact copy_branch_zero state 0 done running countHeld
    have trace := Execution.cons transition (Execution.refl final)
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, 1, max state.liveWords final.liveWords, trace, by simp, ?_, ?_,
      rfl, rfl, rfl, running, countHeld, ?_, rfl, rfl, rfl⟩
    · simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, live, Nat.max_self, Nat.le_refl]
    · change state.heap = state.heap ++ (copiedHeaderWords []).toArray
      simp only [copiedHeaderWords, List.flatMap_nil, copy_nil_array, Array.append_empty]
    · change state.reg 1 = word width cursor
      exact cursorHeld
  | cons row rest ih =>
    intro cursor state position running room cursorFits countFits countHeld cursorHeld
      rankHeld zeroHeld maskHeld rawCell stored
    obtain ⟨queueCell, tagCell, headCell, rankCell, headFits⟩ := stored ⟨0, by simp⟩
    have queueFirst : state.heap[cursor]? = some (word width row.old) := by
      simpa only [List.getElem_cons_zero, Nat.add_zero] using queueCell
    have tagFirst : state.heap[H + 9 + 2 * row.old]? = some (word width row.tag.val) := by
      simpa only [List.getElem_cons_zero] using tagCell
    have headFirst : state.heap[H + 9 + 2 * row.old + 1]? = some (word width row.head) := by
      simpa only [List.getElem_cons_zero] using headCell
    have rankFirst : 3 ≤ row.tag.val → state.heap[rankBase + row.head]? = some row.mapped := by
      simpa only [List.getElem_cons_zero] using rankCell
    have headFitsFirst : row.head < 2 ^ width := by
      simpa only [List.getElem_cons_zero] using headFits
    obtain ⟨middle, firstTicks, firstPeak, firstTrace, firstTime, firstSpace, middleHeap,
      middleStack, middleOutput, middlePC, middleRunning, middleCount, middleCursor,
      middleRank, middleZero, middleMask⟩ := header_row_execution resident nodes base entry done H
        row.old row.head rankBase cursor (row :: rest).length row.mapped row.tag state physical
        position running codeFits (by simp only [List.length_cons] at room; omega)
        countFits (by simp) (by simp only [List.length_cons] at cursorFits; omega)
        headFitsFirst countHeld cursorHeld rankHeld zeroHeld maskHeld rawCell queueFirst
        tagFirst headFirst rankFirst
    have middleSize : middle.heap.size = state.heap.size + 2 := by
      rw [middleHeap]
      simp only [Array.size_push] <;> omega
    have middleLive : middle.liveWords = state.liveWords + 2 := by
      simp only [State.liveWords, middleSize, middleStack, middleOutput]
      omega
    have preserve : ∀ (address : Nat) (value : Word width), state.heap[address]? = some value →
        middle.heap[address]? = some value := by
      intro address value cell
      rw [middleHeap]
      exact copied_pair_preserves state.heap _ _ value address cell
    have restStored : HeaderRowsStored middle.heap H (cursor + 1) rankBase rest := by
      intro index
      obtain ⟨queueOld, tagOld, headOld, rankOld, fitsOld⟩ :=
        stored ⟨index.val + 1, by have := index.isLt; simp only [List.length_cons]; omega⟩
      simp only [List.getElem_cons_succ] at queueOld tagOld headOld rankOld fitsOld
      refine ⟨?_, preserve _ _ tagOld, preserve _ _ headOld, ?_, fitsOld⟩
      · have kept := preserve _ _ queueOld
        simpa only [Nat.add_assoc, Nat.add_comm 1 index.val] using kept
      · intro needsRank
        exact preserve _ _ (rankOld needsRank)
    obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, finalHeap,
      finalStack, finalOutput, finalPC, finalRunning, finalCount, finalCursor,
      finalRank, finalZero, finalMask⟩ := ih (cursor + 1) middle middlePC middleRunning
        (by simp only [List.length_cons] at room; rw [middleSize]; omega)
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [List.length_cons] at countFits; omega)
        (by simpa only [List.length_cons, Nat.add_sub_cancel] using middleCount)
        middleCursor (middleRank.trans rankHeld) (middleZero.trans zeroHeld)
        (middleMask.trans maskHeld) (preserve _ _ rawCell) restStored
    refine ⟨final, firstTicks + restTicks, max firstPeak restPeak,
      firstTrace.append restTrace, ?_, ?_, ?_, finalStack.trans middleStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, finalCount, ?_,
      finalRank.trans middleRank, finalZero.trans middleZero, finalMask.trans middleMask⟩
    · simp only [List.length_cons]
      omega
    · rw [max_le_iff]
      constructor <;> simp only [List.length_cons] <;> omega
    · rw [finalHeap, middleHeap]
      have words : copiedHeaderWords (row :: rest) =
          word width row.tag.val :: row.resultHead :: copiedHeaderWords rest := by
        unfold copiedHeaderWords
        rw [List.flatMap_cons]
        rfl
      rw [words]
      exact copy_pair_array state.heap (word width row.tag.val) row.resultHead (copiedHeaderWords rest)
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 rest.length] using finalCursor


theorem copy_five_array {α : Type} (heap : Array α) (a b c d e : α) :
    ((((heap.push a).push b).push c).push d).push e = heap ++ #[a, b, c, d, e] := by
  simp only [Array.push_eq_append, Array.append_assoc]
  rfl

theorem copyRegisters_initial_rank (state : State width 8) (rankBase : Nat)
    (rankHeld : state.reg 4 = word width rankBase) :
    state.reg = copyRegisters (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3)
      (word width rankBase) (state.reg 5) (state.reg 6) (state.reg 7) := by
  funext register
  fin_cases register <;> simp [copyRegisters, rankHeld]

theorem copy_store_step (state : State width 8) (addressReg sourceReg : Fin 8)
    (address : Nat) (value : Word width) (running : state.halted = false)
    (valid : address < state.heap.size) (fits : address < 2 ^ width)
    (addressHeld : state.reg addressReg = word width address)
    (valueHeld : state.reg sourceReg = value) :
    step (.store addressReg sourceReg) state = some
      { state.advance with heap := state.heap.setIfInBounds address value } := by
  simp only [step, running, Bool.false_eq_true, ite_false, addressHeld,
    show (word width address).val = address from Nat.mod_eq_of_lt fits,
    dite_eq_left valid, valueHeld, Array.setIfInBounds, dite_eq_left valid]

theorem typed_origin_store_preserves (heap : Array (Word width)) (slot H : Nat)
    (origin : Word width) (below : slot < H) (address : Nat) (afterSource : H ≤ address)
    (value : Word width) (cell : heap[address]? = some value) :
    (heap.setIfInBounds slot origin)[address]? = some value := by
  have different : slot ≠ address := by omega
  obtain ⟨valid, actual⟩ := Array.getElem?_eq_some_iff.mp cell
  rw [Array.getElem?_eq_getElem (by simpa only [Array.size_setIfInBounds] using valid)]
  rw [Array.getElem_setIfInBounds_ne valid different, actual]

-- Exact source fields, not new metadata supplied from a semantic graph query.
def RawGlobalCells (heap : Array (Word width))
    (H nodes channels roots children guards : Nat) : Prop :=
  heap[H]? = some (word width nodes) ∧
  heap[H + 1]? = some (word width channels) ∧
  heap[H + 2]? = some (word width roots) ∧
  heap[H + 3]? = some (word width children) ∧
  heap[H + 4]? = some (word width guards)

-- The one setup store places the dynamically derived typed allocation origin
-- in dead nextSlot. Every later packet source and actual rank cell is ≥H,
-- while nextSlot<H is inherited from the completed dependency heap layout.
-- The fetched permutation 1,0,3,4,2 gives exact typed [n,V,E,U,R].

theorem typed_global_execution (resident : Program width 8)
    (nodes channels roots children guards base entry headerEntry H rankBase : Nat)
    (state : State width 8)
    (physical : ∀ phase : Fin 31, resident[entry + phase.val]? =
      (typedGlobalCopyCode width nodes base headerEntry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 31 < 2 ^ width) (room : state.heap.size + 5 < 2 ^ width)
    (allocation : state.heap.size = rankBase + nodes)
    (rankHeld : state.reg 4 = word width rankBase)
    (below : Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base < H)
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (globalCells : RawGlobalCells state.heap H nodes channels roots children guards) :
    ∃ final peak, Execution resident state final 31 peak ∧ peak ≤ state.liveWords + 5 ∧
      final.heap = state.heap.setIfInBounds
        (Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base) (word width state.heap.size) ++
          #[word width channels, word width nodes, word width children, word width guards, word width roots] ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width headerEntry ∧ final.halted = false ∧
      final.reg 0 = word width nodes ∧
      final.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) := by
  obtain ⟨cell0, cell1, cell2, cell3, cell4⟩ := globalCells
  obtain ⟨sourceBound, sourceValue⟩ := Array.getElem?_eq_some_iff.mp cell4
  obtain ⟨activeBound, activeValue⟩ := Array.getElem?_eq_some_iff.mp rawCell
  let slot := Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base
  let active := Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base
  have slotValid : slot < state.heap.size := by change Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base < _; omega
  have slotFits : slot < 2 ^ width := by omega
  have activeFits : active < 2 ^ width := by
    dsimp only [active]
    omega
  have activeDifferent : slot ≠ active := by
    simp only [slot, active, Controller.Horn.WorklistBucketReady.nextSlot, Controller.Horn.WorklistFIFO.activeSlot]
    omega
  have Hfits : H < 2 ^ width := by omega
  have rankFits : rankBase < 2 ^ width := by omega
  have nodeFits : nodes < 2 ^ width := by omega
  let s1 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (state.reg 2) (word width (nodes)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7)
      heap := state.heap, pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (state.reg 2) (word width (state.heap.size)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7)
      heap := state.heap, pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (slot)) (word width (state.heap.size)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7)
      heap := state.heap, pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (slot)) (word width (state.heap.size)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7)
      heap := state.heap.setIfInBounds slot (word width state.heap.size), pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (active)) (word width (state.heap.size)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7)
      heap := state.heap.setIfInBounds slot (word width state.heap.size), pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (state.heap.size)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7)
      heap := state.heap.setIfInBounds slot (word width state.heap.size), pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (1)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7)
      heap := state.heap.setIfInBounds slot (word width state.heap.size), pc := word width (entry + 7) }
  let s8 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (1)) (word width (rankBase)) (word width (H + 1)) (state.reg 6) (state.reg 7)
      heap := state.heap.setIfInBounds slot (word width state.heap.size), pc := word width (entry + 8) }
  let s9 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (1)) (word width (rankBase)) (word width (channels)) (state.reg 6) (state.reg 7)
      heap := state.heap.setIfInBounds slot (word width state.heap.size), pc := word width (entry + 9) }
  let s10 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (1)) (word width (rankBase)) (word width (channels)) (state.reg 6) (state.reg 7)
      heap := (state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels)), pc := word width (entry + 10) }
  let s11 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (0)) (word width (rankBase)) (word width (channels)) (state.reg 6) (state.reg 7)
      heap := (state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels)), pc := word width (entry + 11) }
  let s12 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (0)) (word width (rankBase)) (word width (H + 0)) (state.reg 6) (state.reg 7)
      heap := (state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels)), pc := word width (entry + 12) }
  let s13 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (0)) (word width (rankBase)) (word width (nodes)) (state.reg 6) (state.reg 7)
      heap := (state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels)), pc := word width (entry + 13) }
  let s14 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (0)) (word width (rankBase)) (word width (nodes)) (state.reg 6) (state.reg 7)
      heap := ((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes)), pc := word width (entry + 14) }
  let s15 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (3)) (word width (rankBase)) (word width (nodes)) (state.reg 6) (state.reg 7)
      heap := ((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes)), pc := word width (entry + 15) }
  let s16 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (3)) (word width (rankBase)) (word width (H + 3)) (state.reg 6) (state.reg 7)
      heap := ((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes)), pc := word width (entry + 16) }
  let s17 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (3)) (word width (rankBase)) (word width (children)) (state.reg 6) (state.reg 7)
      heap := ((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes)), pc := word width (entry + 17) }
  let s18 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (3)) (word width (rankBase)) (word width (children)) (state.reg 6) (state.reg 7)
      heap := (((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children)), pc := word width (entry + 18) }
  let s19 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (4)) (word width (rankBase)) (word width (children)) (state.reg 6) (state.reg 7)
      heap := (((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children)), pc := word width (entry + 19) }
  let s20 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (4)) (word width (rankBase)) (word width (H + 4)) (state.reg 6) (state.reg 7)
      heap := (((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children)), pc := word width (entry + 20) }
  let s21 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (4)) (word width (rankBase)) (word width (guards)) (state.reg 6) (state.reg 7)
      heap := (((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children)), pc := word width (entry + 21) }
  let s22 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (4)) (word width (rankBase)) (word width (guards)) (state.reg 6) (state.reg 7)
      heap := ((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))).push (word width (guards)), pc := word width (entry + 22) }
  let s23 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (2)) (word width (rankBase)) (word width (guards)) (state.reg 6) (state.reg 7)
      heap := ((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))).push (word width (guards)), pc := word width (entry + 23) }
  let s24 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (2)) (word width (rankBase)) (word width (H + 2)) (state.reg 6) (state.reg 7)
      heap := ((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))).push (word width (guards)), pc := word width (entry + 24) }
  let s25 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (2)) (word width (rankBase)) (word width (roots)) (state.reg 6) (state.reg 7)
      heap := ((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))).push (word width (guards)), pc := word width (entry + 25) }
  let s26 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (H)) (word width (2)) (word width (rankBase)) (word width (roots)) (state.reg 6) (state.reg 7)
      heap := (((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))).push (word width (guards))).push (word width (roots)), pc := word width (entry + 26) }
  let s27 : State width 8 := { state with
      reg := copyRegisters (word width (nodes)) (state.reg 1) (word width (H)) (word width (2)) (word width (rankBase)) (word width (roots)) (state.reg 6) (state.reg 7)
      heap := (((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))).push (word width (guards))).push (word width (roots)), pc := word width (entry + 27) }
  let s28 : State width 8 := { state with
      reg := copyRegisters (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (H)) (word width (2)) (word width (rankBase)) (word width (roots)) (state.reg 6) (state.reg 7)
      heap := (((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))).push (word width (guards))).push (word width (roots)), pc := word width (entry + 28) }
  let s29 : State width 8 := { state with
      reg := copyRegisters (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (H)) (word width (2)) (word width (rankBase)) (word width (roots)) (word width (0)) (state.reg 7)
      heap := (((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))).push (word width (guards))).push (word width (roots)), pc := word width (entry + 29) }
  let s30 : State width 8 := { state with
      reg := copyRegisters (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (H)) (word width (2)) (word width (rankBase)) (word width (roots)) (word width (0)) (word width (2 ^ width - 1))
      heap := (((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))).push (word width (guards))).push (word width (roots)), pc := word width (entry + 30) }
  let s31 : State width 8 := { state with
      reg := copyRegisters (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (H)) (word width (2)) (word width (rankBase)) (word width (roots)) (word width (0)) (word width (2 ^ width - 1))
      heap := (((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))).push (word width (guards))).push (word width (roots)), pc := word width (headerEntry) }
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.constant 3 (word width (nodes))) position (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨0, by decide⟩)]
    have result := copy_constant_step state 3 (word width (nodes)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      change (if register = 3 then word width nodes else state.reg register) = _
      rw [copyRegisters_initial_rank state rankBase rankHeld]
      exact congrFun (copyRegisters_update3 (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (word width rankBase) (state.reg 5) (state.reg 6) (state.reg 7) (word width (nodes))) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s1, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.add 3 4 3) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨1, by decide⟩)]
    have result := copy_add_step s1 3 4 3 (rankBase) (nodes) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (rankBase) + (nodes) = (state.heap.size) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (state.reg 0) (state.reg 1) (state.reg 2) (word width (nodes)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7) (word width (state.heap.size))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s2, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.constant 2 (word width (slot))) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨2, by decide⟩)]
    have result := copy_constant_step s2 2 (word width (slot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (state.reg 0) (state.reg 1) (state.reg 2) (word width (state.heap.size)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7) (word width (slot))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords + 0 := by
    simp only [s3, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.store 2 3) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨3, by decide⟩)]
    have result := copy_store_step s3 2 3 slot (word width state.heap.size) running slotValid slotFits (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords + 0 := by
    simp only [s4, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.constant 2 (word width (active))) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨4, by decide⟩)]
    have result := copy_constant_step s4 2 (word width (active)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (state.reg 0) (state.reg 1) (word width (slot)) (word width (state.heap.size)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7) (word width (active))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords + 0 := by
    simp only [s5, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.load 2 2) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨5, by decide⟩)]
    have result := copy_load_step s5 2 2 (active) (word width (H)) running activeFits (by rfl) (by
        change (state.heap.setIfInBounds slot (word width state.heap.size))[active]? = some (word width (H))
        have preserved : (state.heap.setIfInBounds slot (word width state.heap.size))[active]? = some (word width (H)) := by
          simp only [Array.getElem?_setIfInBounds, activeDifferent, ite_false]
          exact rawCell
        exact preserved)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (state.reg 0) (state.reg 1) (word width (active)) (word width (state.heap.size)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords + 0 := by
    simp only [s6, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 3 (word width (1))) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨6, by decide⟩)]
    have result := copy_constant_step s6 3 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (state.reg 0) (state.reg 1) (word width (H)) (word width (state.heap.size)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords + 0 := by
    simp only [s7, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 5 2 3) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨7, by decide⟩)]
    have result := copy_add_step s7 5 2 3 (H) (1) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H) + (1) = (H + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (1)) (word width (rankBase)) (state.reg 5) (state.reg 6) (state.reg 7) (word width (H + 1))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords + 0 := by
    simp only [s8, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.load 5 5) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨8, by decide⟩)]
    have result := copy_load_step s8 5 5 (H + 1) (word width (channels)) running (by omega) (by rfl) (by
        change (state.heap.setIfInBounds slot (word width state.heap.size))[H + 1]? = some (word width (channels))
        have preserved : (state.heap.setIfInBounds slot (word width state.heap.size))[H + 1]? = some (word width (channels)) := by
          exact typed_origin_store_preserves state.heap slot H _ below (H + 1) (by omega) _ cell1
        exact preserved)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (1)) (word width (rankBase)) (word width (H + 1)) (state.reg 6) (state.reg 7) (word width (channels))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords + 0 := by
    simp only [s9, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨9, by decide⟩)]
    have result := copy_allocate_step s9 5 (word width (channels)) running (by simp only [s9, Array.size_push, Array.size_setIfInBounds]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords + 1 := by
    simp only [s10, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.constant 3 (word width (0))) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨10, by decide⟩)]
    have result := copy_constant_step s10 3 (word width (0)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (state.reg 0) (state.reg 1) (word width (H)) (word width (1)) (word width (rankBase)) (word width (channels)) (state.reg 6) (state.reg 7) (word width (0))) register
    · rfl
    · rfl
    · rfl
    · change s10.advance.pc = word width (entry + 11)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s10
        (entry + 10) (by rfl) (by omega)
    · rfl
  have live11 : s11.liveWords = state.liveWords + 1 := by
    simp only [s11, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t11 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.add 5 2 3) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨11, by decide⟩)]
    have result := copy_add_step s11 5 2 3 (H) (0) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H) + (0) = (H + 0) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (0)) (word width (rankBase)) (word width (channels)) (state.reg 6) (state.reg 7) (word width (H + 0))) register
    · rfl
    · rfl
    · rfl
    · change s11.advance.pc = word width (entry + 12)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s11
        (entry + 11) (by rfl) (by omega)
    · rfl
  have live12 : s12.liveWords = state.liveWords + 1 := by
    simp only [s12, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t12 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.load 5 5) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨12, by decide⟩)]
    have result := copy_load_step s12 5 5 (H + 0) (word width (nodes)) running (by omega) (by rfl) (by
        change ((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels)))[H + 0]? = some (word width (nodes))
        have preserved : (state.heap.setIfInBounds slot (word width state.heap.size))[H + 0]? = some (word width (nodes)) := by
          exact typed_origin_store_preserves state.heap slot H _ below (H + 0) (by omega) _ cell0
        have preserved1 := copy_push_cell (state.heap.setIfInBounds slot (word width state.heap.size)) (word width (channels)) _ _ preserved
        exact preserved1)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (0)) (word width (rankBase)) (word width (H + 0)) (state.reg 6) (state.reg 7) (word width (nodes))) register
    · rfl
    · rfl
    · rfl
    · change s12.advance.pc = word width (entry + 13)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s12
        (entry + 12) (by rfl) (by omega)
    · rfl
  have live13 : s13.liveWords = state.liveWords + 1 := by
    simp only [s13, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t13 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨13, by decide⟩)]
    have result := copy_allocate_step s13 5 (word width (nodes)) running (by simp only [s13, Array.size_push, Array.size_setIfInBounds]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s13.advance.pc = word width (entry + 14)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s13
        (entry + 13) (by rfl) (by omega)
    · rfl
  have live14 : s14.liveWords = state.liveWords + 2 := by
    simp only [s14, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t14 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 14) (.constant 3 (word width (3))) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨14, by decide⟩)]
    have result := copy_constant_step s14 3 (word width (3)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (state.reg 0) (state.reg 1) (word width (H)) (word width (0)) (word width (rankBase)) (word width (nodes)) (state.reg 6) (state.reg 7) (word width (3))) register
    · rfl
    · rfl
    · rfl
    · change s14.advance.pc = word width (entry + 15)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s14
        (entry + 14) (by rfl) (by omega)
    · rfl
  have live15 : s15.liveWords = state.liveWords + 2 := by
    simp only [s15, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t15 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 15) (.add 5 2 3) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨15, by decide⟩)]
    have result := copy_add_step s15 5 2 3 (H) (3) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H) + (3) = (H + 3) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (3)) (word width (rankBase)) (word width (nodes)) (state.reg 6) (state.reg 7) (word width (H + 3))) register
    · rfl
    · rfl
    · rfl
    · change s15.advance.pc = word width (entry + 16)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s15
        (entry + 15) (by rfl) (by omega)
    · rfl
  have live16 : s16.liveWords = state.liveWords + 2 := by
    simp only [s16, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t16 : programStep resident s16 = some s17 := by
    rw [fetched resident s16 (entry + 16) (.load 5 5) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨16, by decide⟩)]
    have result := copy_load_step s16 5 5 (H + 3) (word width (children)) running (by omega) (by rfl) (by
        change (((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes)))[H + 3]? = some (word width (children))
        have preserved : (state.heap.setIfInBounds slot (word width state.heap.size))[H + 3]? = some (word width (children)) := by
          exact typed_origin_store_preserves state.heap slot H _ below (H + 3) (by omega) _ cell3
        have preserved1 := copy_push_cell (state.heap.setIfInBounds slot (word width state.heap.size)) (word width (channels)) _ _ preserved
        have preserved2 := copy_push_cell ((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))) (word width (nodes)) _ _ preserved1
        exact preserved2)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (3)) (word width (rankBase)) (word width (H + 3)) (state.reg 6) (state.reg 7) (word width (children))) register
    · rfl
    · rfl
    · rfl
    · change s16.advance.pc = word width (entry + 17)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s16
        (entry + 16) (by rfl) (by omega)
    · rfl
  have live17 : s17.liveWords = state.liveWords + 2 := by
    simp only [s17, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t17 : programStep resident s17 = some s18 := by
    rw [fetched resident s17 (entry + 17) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨17, by decide⟩)]
    have result := copy_allocate_step s17 5 (word width (children)) running (by simp only [s17, Array.size_push, Array.size_setIfInBounds]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s17.advance.pc = word width (entry + 18)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s17
        (entry + 17) (by rfl) (by omega)
    · rfl
  have live18 : s18.liveWords = state.liveWords + 3 := by
    simp only [s18, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t18 : programStep resident s18 = some s19 := by
    rw [fetched resident s18 (entry + 18) (.constant 3 (word width (4))) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨18, by decide⟩)]
    have result := copy_constant_step s18 3 (word width (4)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (state.reg 0) (state.reg 1) (word width (H)) (word width (3)) (word width (rankBase)) (word width (children)) (state.reg 6) (state.reg 7) (word width (4))) register
    · rfl
    · rfl
    · rfl
    · change s18.advance.pc = word width (entry + 19)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s18
        (entry + 18) (by rfl) (by omega)
    · rfl
  have live19 : s19.liveWords = state.liveWords + 3 := by
    simp only [s19, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t19 : programStep resident s19 = some s20 := by
    rw [fetched resident s19 (entry + 19) (.add 5 2 3) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨19, by decide⟩)]
    have result := copy_add_step s19 5 2 3 (H) (4) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H) + (4) = (H + 4) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (4)) (word width (rankBase)) (word width (children)) (state.reg 6) (state.reg 7) (word width (H + 4))) register
    · rfl
    · rfl
    · rfl
    · change s19.advance.pc = word width (entry + 20)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s19
        (entry + 19) (by rfl) (by omega)
    · rfl
  have live20 : s20.liveWords = state.liveWords + 3 := by
    simp only [s20, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t20 : programStep resident s20 = some s21 := by
    rw [fetched resident s20 (entry + 20) (.load 5 5) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨20, by decide⟩)]
    have result := copy_load_step s20 5 5 (H + 4) (word width (guards)) running (by omega) (by rfl) (by
        change ((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children)))[H + 4]? = some (word width (guards))
        have preserved : (state.heap.setIfInBounds slot (word width state.heap.size))[H + 4]? = some (word width (guards)) := by
          exact typed_origin_store_preserves state.heap slot H _ below (H + 4) (by omega) _ cell4
        have preserved1 := copy_push_cell (state.heap.setIfInBounds slot (word width state.heap.size)) (word width (channels)) _ _ preserved
        have preserved2 := copy_push_cell ((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))) (word width (nodes)) _ _ preserved1
        have preserved3 := copy_push_cell (((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))) (word width (children)) _ _ preserved2
        exact preserved3)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (4)) (word width (rankBase)) (word width (H + 4)) (state.reg 6) (state.reg 7) (word width (guards))) register
    · rfl
    · rfl
    · rfl
    · change s20.advance.pc = word width (entry + 21)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s20
        (entry + 20) (by rfl) (by omega)
    · rfl
  have live21 : s21.liveWords = state.liveWords + 3 := by
    simp only [s21, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t21 : programStep resident s21 = some s22 := by
    rw [fetched resident s21 (entry + 21) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨21, by decide⟩)]
    have result := copy_allocate_step s21 5 (word width (guards)) running (by simp only [s21, Array.size_push, Array.size_setIfInBounds]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s21.advance.pc = word width (entry + 22)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s21
        (entry + 21) (by rfl) (by omega)
    · rfl
  have live22 : s22.liveWords = state.liveWords + 4 := by
    simp only [s22, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t22 : programStep resident s22 = some s23 := by
    rw [fetched resident s22 (entry + 22) (.constant 3 (word width (2))) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨22, by decide⟩)]
    have result := copy_constant_step s22 3 (word width (2)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (state.reg 0) (state.reg 1) (word width (H)) (word width (4)) (word width (rankBase)) (word width (guards)) (state.reg 6) (state.reg 7) (word width (2))) register
    · rfl
    · rfl
    · rfl
    · change s22.advance.pc = word width (entry + 23)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s22
        (entry + 22) (by rfl) (by omega)
    · rfl
  have live23 : s23.liveWords = state.liveWords + 4 := by
    simp only [s23, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t23 : programStep resident s23 = some s24 := by
    rw [fetched resident s23 (entry + 23) (.add 5 2 3) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨23, by decide⟩)]
    have result := copy_add_step s23 5 2 3 (H) (2) running (by omega) (by omega) (by rfl) (by rfl)
    have scalar : (H) + (2) = (H + 2) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (2)) (word width (rankBase)) (word width (guards)) (state.reg 6) (state.reg 7) (word width (H + 2))) register
    · rfl
    · rfl
    · rfl
    · change s23.advance.pc = word width (entry + 24)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s23
        (entry + 23) (by rfl) (by omega)
    · rfl
  have live24 : s24.liveWords = state.liveWords + 4 := by
    simp only [s24, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t24 : programStep resident s24 = some s25 := by
    rw [fetched resident s24 (entry + 24) (.load 5 5) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨24, by decide⟩)]
    have result := copy_load_step s24 5 5 (H + 2) (word width (roots)) running (by omega) (by rfl) (by
        change (((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))).push (word width (guards)))[H + 2]? = some (word width (roots))
        have preserved : (state.heap.setIfInBounds slot (word width state.heap.size))[H + 2]? = some (word width (roots)) := by
          exact typed_origin_store_preserves state.heap slot H _ below (H + 2) (by omega) _ cell2
        have preserved1 := copy_push_cell (state.heap.setIfInBounds slot (word width state.heap.size)) (word width (channels)) _ _ preserved
        have preserved2 := copy_push_cell ((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))) (word width (nodes)) _ _ preserved1
        have preserved3 := copy_push_cell (((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))) (word width (children)) _ _ preserved2
        have preserved4 := copy_push_cell ((((state.heap.setIfInBounds slot (word width state.heap.size)).push (word width (channels))).push (word width (nodes))).push (word width (children))) (word width (guards)) _ _ preserved3
        exact preserved4)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (H)) (word width (2)) (word width (rankBase)) (word width (H + 2)) (state.reg 6) (state.reg 7) (word width (roots))) register
    · rfl
    · rfl
    · rfl
    · change s24.advance.pc = word width (entry + 25)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s24
        (entry + 24) (by rfl) (by omega)
    · rfl
  have live25 : s25.liveWords = state.liveWords + 4 := by
    simp only [s25, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t25 : programStep resident s25 = some s26 := by
    rw [fetched resident s25 (entry + 25) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨25, by decide⟩)]
    have result := copy_allocate_step s25 5 (word width (roots)) running (by simp only [s25, Array.size_push, Array.size_setIfInBounds]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s25.advance.pc = word width (entry + 26)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s25
        (entry + 25) (by rfl) (by omega)
    · rfl
  have live26 : s26.liveWords = state.liveWords + 5 := by
    simp only [s26, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t26 : programStep resident s26 = some s27 := by
    rw [fetched resident s26 (entry + 26) (.constant 0 (word width (nodes))) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨26, by decide⟩)]
    have result := copy_constant_step s26 0 (word width (nodes)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (state.reg 0) (state.reg 1) (word width (H)) (word width (2)) (word width (rankBase)) (word width (roots)) (state.reg 6) (state.reg 7) (word width (nodes))) register
    · rfl
    · rfl
    · rfl
    · change s26.advance.pc = word width (entry + 27)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s26
        (entry + 26) (by rfl) (by omega)
    · rfl
  have live27 : s27.liveWords = state.liveWords + 5 := by
    simp only [s27, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t27 : programStep resident s27 = some s28 := by
    rw [fetched resident s27 (entry + 27) (.constant 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base))) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨27, by decide⟩)]
    have result := copy_constant_step s27 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (nodes)) (state.reg 1) (word width (H)) (word width (2)) (word width (rankBase)) (word width (roots)) (state.reg 6) (state.reg 7) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base))) register
    · rfl
    · rfl
    · rfl
    · change s27.advance.pc = word width (entry + 28)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s27
        (entry + 27) (by rfl) (by omega)
    · rfl
  have live28 : s28.liveWords = state.liveWords + 5 := by
    simp only [s28, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t28 : programStep resident s28 = some s29 := by
    rw [fetched resident s28 (entry + 28) (.constant 6 (word width (0))) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨28, by decide⟩)]
    have result := copy_constant_step s28 6 (word width (0)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update6 (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (H)) (word width (2)) (word width (rankBase)) (word width (roots)) (state.reg 6) (state.reg 7) (word width (0))) register
    · rfl
    · rfl
    · rfl
    · change s28.advance.pc = word width (entry + 29)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s28
        (entry + 28) (by rfl) (by omega)
    · rfl
  have live29 : s29.liveWords = state.liveWords + 5 := by
    simp only [s29, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t29 : programStep resident s29 = some s30 := by
    rw [fetched resident s29 (entry + 29) (.constant 7 (word width (2 ^ width - 1))) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨29, by decide⟩)]
    have result := copy_constant_step s29 7 (word width (2 ^ width - 1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update7 (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (H)) (word width (2)) (word width (rankBase)) (word width (roots)) (word width (0)) (state.reg 7) (word width (2 ^ width - 1))) register
    · rfl
    · rfl
    · rfl
    · change s29.advance.pc = word width (entry + 30)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s29
        (entry + 29) (by rfl) (by omega)
    · rfl
  have live30 : s30.liveWords = state.liveWords + 5 := by
    simp only [s30, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t30 : programStep resident s30 = some s31 := by
    rw [fetched resident s30 (entry + 30) (.branchZero 6 (word width headerEntry)) (by rfl) (by omega)
      (by simpa [typedGlobalCopyCode] using physical ⟨30, by decide⟩)]
    have result := copy_branch_zero s30 6 headerEntry running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live31 : s31.liveWords = state.liveWords + 5 := by
    simp only [s31, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.cons t16 (Execution.cons t17 (Execution.cons t18 (Execution.cons t19 (Execution.cons t20 (Execution.cons t21 (Execution.cons t22 (Execution.cons t23 (Execution.cons t24 (Execution.cons t25 (Execution.cons t26 (Execution.cons t27 (Execution.cons t28 (Execution.cons t29 (Execution.cons t30 (Execution.refl s31)))))))))))))))))))))))))))))))
  refine ⟨s31, max state.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords (max s4.liveWords (max s5.liveWords (max s6.liveWords (max s7.liveWords (max s8.liveWords (max s9.liveWords (max s10.liveWords (max s11.liveWords (max s12.liveWords (max s13.liveWords (max s14.liveWords (max s15.liveWords (max s16.liveWords (max s17.liveWords (max s18.liveWords (max s19.liveWords (max s20.liveWords (max s21.liveWords (max s22.liveWords (max s23.liveWords (max s24.liveWords (max s25.liveWords (max s26.liveWords (max s27.liveWords (max s28.liveWords (max s29.liveWords (max s30.liveWords (s31.liveWords))))))))))))))))))))))))))))))), ?_, ?_, ?_, rfl, rfl, rfl, running, rfl, rfl, rankHeld.symm, rfl, rfl⟩
  · simpa only [Nat.reduceAdd] using trace
  · simp only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, live14, live15, live16, live17, live18, live19, live20, live21, live22, live23, live24, live25, live26, live27, live28, live29, live30, live31, max_le_iff]
    omega
  · change (((((state.heap.setIfInBounds slot (word width state.heap.size)).push
      (word width channels)).push (word width nodes)).push (word width children)).push
      (word width guards)).push (word width roots) = _
    exact copy_five_array _ _ _ _ _ _

-- Consumer of the retained original child/root stream and the actual produced rank heap.
def mappedOccurrenceCopyCode (width entry done : Nat) : Program width 8 :=
  #[.branchZero 3 (word width done), .load 5 2, .add 5 5 4, .load 5 5,
    .allocate 5, .constant 5 (word width 1), .add 2 2 5, .add 3 3 7,
    .branchZero 6 (word width entry)]

theorem mapped_occurrence_execution (resident : Program width 8)
    (entry done cursor count rankBase original : Nat) (mapped : Word width)
    (state : State width 8)
    (physical : ∀ phase : Fin 9, resident[entry + phase.val]? =
      (mappedOccurrenceCopyCode width entry done)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 9 < 2 ^ width) (room : state.heap.size + 1 < 2 ^ width)
    (countFits : count < 2 ^ width) (positive : 0 < count)
    (cursorFits : cursor + 1 < 2 ^ width) (originalFits : original < 2 ^ width)
    (cursorHeld : state.reg 2 = word width cursor) (countHeld : state.reg 3 = word width count)
    (rankHeld : state.reg 4 = word width rankBase) (zeroHeld : state.reg 6 = word width 0)
    (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (sourceCell : state.heap[cursor]? = some (word width original))
    (rankCell : state.heap[rankBase + original]? = some mapped) :
    ∃ final peak, Execution resident state final 9 peak ∧ peak ≤ state.liveWords + 1 ∧
      final.heap = state.heap.push mapped ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 2 = word width (cursor + 1) ∧ final.reg 3 = word width (count - 1) ∧
      (∀ register : Fin 8, register ≠ 2 → register ≠ 3 → register ≠ 5 →
        final.reg register = state.reg register) := by
  let s1 : State width 8 := state.advance
  let s2 : State width 8 := s1.advance.put 5 (word width original)
  let s3 : State width 8 := s2.advance.put 5 (word width (rankBase + original))
  let s4 : State width 8 := s3.advance.put 5 mapped
  let s5 : State width 8 := { s4.advance with heap := state.heap.push mapped }
  let s6 : State width 8 := s5.advance.put 5 (word width 1)
  let s7 : State width 8 := s6.advance.put 2 (word width (cursor + 1))
  let s8 : State width 8 := s7.advance.put 3 (word width (count - 1))
  let s9 : State width 8 := { s8.advance with pc := word width entry }
  obtain ⟨rankBound, rankValue⟩ := Array.getElem?_eq_some_iff.mp rankCell
  have rankFits : rankBase < 2 ^ width := by omega
  have addressFits : rankBase + original < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pc1 : s1.pc = word width (entry + 1) := by
    change state.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
      (entry + 0) position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
      (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
      (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    change s3.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
      (entry + 3) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := by
    change s4.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
      (entry + 4) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 6) := by
    change s5.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
      (entry + 5) pc5 (by omega)
  have pc7 : s7.pc = word width (entry + 7) := by
    change s6.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
      (entry + 6) pc6 (by omega)
  have pc8 : s8.pc = word width (entry + 8) := by
    change s7.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
      (entry + 7) pc7 (by omega)
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.branchZero 3 (word width done))
      position (by omega)
      (by simpa [mappedOccurrenceCopyCode] using physical ⟨0, by decide⟩)]
    exact copy_branch_nonzero state 3 done count running positive countFits countHeld
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.load 5 2)
      pc1 (by omega)
      (by simpa [mappedOccurrenceCopyCode] using physical ⟨1, by decide⟩)]
    apply copy_load_step s1 5 2 cursor (word width original)
    · exact running
    · omega
    · exact cursorHeld
    · exact sourceCell
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.add 5 5 4)
      pc2 (by omega)
      (by simpa [mappedOccurrenceCopyCode] using physical ⟨2, by decide⟩)]
    have value : step (.add 5 5 4) s2 =
        some (s2.advance.put 5 (word width (original + rankBase))) :=
      copy_add_step s2 5 5 4 original rankBase running originalFits rankFits
        (by simp [s2, State.put]) (by simp [s2, s1, State.put, State.advance, rankHeld])
    simpa only [Nat.add_comm original rankBase] using value
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.load 5 5)
      pc3 (by omega)
      (by simpa [mappedOccurrenceCopyCode] using physical ⟨3, by decide⟩)]
    apply copy_load_step s3 5 5 (rankBase + original) mapped
    · exact running
    · exact addressFits
    · simp [s3, State.put]
    · exact rankCell
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.allocate 5)
      pc4 (by omega)
      (by simpa [mappedOccurrenceCopyCode] using physical ⟨4, by decide⟩)]
    exact copy_allocate_step s4 5 mapped running (by change state.heap.size < _; omega)
      (by simp [s4, State.put])
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.constant 5 (word width 1))
      pc5 (by omega)
      (by simpa [mappedOccurrenceCopyCode] using physical ⟨5, by decide⟩)]
    exact copy_constant_step s5 5 (word width 1) running
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.add 2 2 5)
      pc6 (by omega)
      (by simpa [mappedOccurrenceCopyCode] using physical ⟨6, by decide⟩)]
    exact copy_add_step s6 2 2 5 cursor 1 running (by omega) (by omega)
      (by simp [s6, s5, s4, s3, s2, s1, State.put, State.advance, cursorHeld])
      (by simp [s6, State.put])
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 3 3 7)
      pc7 (by omega)
      (by simpa [mappedOccurrenceCopyCode] using physical ⟨7, by decide⟩)]
    have value := copy_add_step s7 3 3 7 count (2 ^ width - 1) running countFits maskFits
      (by simp [s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, countHeld])
      (by simp [s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, maskHeld])
    simpa only [marker_word_decrement count positive countFits] using value
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.branchZero 6 (word width entry))
      pc8 (by omega)
      (by simpa [mappedOccurrenceCopyCode] using physical ⟨8, by decide⟩)]
    exact copy_branch_zero s8 6 entry running
      (by simp [s8, s7, s6, s5, s4, s3, s2, s1, State.put, State.advance, zeroHeld])
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s1, State.advance, State.put, State.liveWords, Array.size_push] <;> omega
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s2, s1, State.advance, State.put, State.liveWords, Array.size_push] <;> omega
  have live3 : s3.liveWords = state.liveWords + 0 := by
    simp only [s3, s2, s1, State.advance, State.put, State.liveWords, Array.size_push] <;> omega
  have live4 : s4.liveWords = state.liveWords + 0 := by
    simp only [s4, s3, s2, s1, State.advance, State.put, State.liveWords, Array.size_push] <;> omega
  have live5 : s5.liveWords = state.liveWords + 1 := by
    simp only [s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, Array.size_push] <;> omega
  have live6 : s6.liveWords = state.liveWords + 1 := by
    simp only [s6, s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, Array.size_push] <;> omega
  have live7 : s7.liveWords = state.liveWords + 1 := by
    simp only [s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, Array.size_push] <;> omega
  have live8 : s8.liveWords = state.liveWords + 1 := by
    simp only [s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, Array.size_push] <;> omega
  have live9 : s9.liveWords = state.liveWords + 1 := by
    simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put, State.liveWords, Array.size_push] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl s9)))))))))
  refine ⟨s9, max state.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords (max s4.liveWords (max s5.liveWords (max s6.liveWords (max s7.liveWords (max s8.liveWords (s9.liveWords))))))))), ?_, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_⟩
  · simpa only [Nat.reduceAdd] using trace
  · simp only [live1, live2, live3, live4, live5, live6, live7, live8, live9, Nat.add_zero, max_le_iff]
    omega
  · simp [s9, s8, s7, State.advance, State.put]
  · simp [s9, s8, State.advance, State.put]
  · intro register notCursor notCount notTemporary
    simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put,
      notCursor, notCount, notTemporary]

structure MappedOccurrence (width : Nat) where
  original : Nat
  mapped : Word width

def MappedStreamStored (heap : Array (Word width)) (cursor rankBase : Nat)
    (occurrences : List (MappedOccurrence width)) : Prop :=
  ∀ index : Fin occurrences.length,
    let occurrence := occurrences[index.val]
    heap[cursor + index.val]? = some (word width occurrence.original) ∧
    heap[rankBase + occurrence.original]? = some occurrence.mapped ∧
    occurrence.original < 2 ^ width

theorem mapped_stream_execution (resident : Program width 8) (entry done rankBase : Nat)
    (physical : ∀ phase : Fin 9, resident[entry + phase.val]? =
      (mappedOccurrenceCopyCode width entry done)[phase.val]?)
    (codeFits : entry + 9 < 2 ^ width) :
    ∀ (occurrences : List (MappedOccurrence width)) (cursor : Nat) (state : State width 8),
    state.pc = word width entry → state.halted = false →
    state.heap.size + occurrences.length < 2 ^ width →
    cursor + occurrences.length < 2 ^ width → occurrences.length < 2 ^ width →
    state.reg 2 = word width cursor → state.reg 3 = word width occurrences.length →
    state.reg 4 = word width rankBase → state.reg 6 = word width 0 →
    state.reg 7 = word width (2 ^ width - 1) →
    MappedStreamStored state.heap cursor rankBase occurrences →
    ∃ final peak, Execution resident state final (9 * occurrences.length + 1) peak ∧
      peak ≤ state.liveWords + occurrences.length ∧
      final.heap = state.heap ++ (occurrences.map MappedOccurrence.mapped).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.reg 2 = word width (cursor + occurrences.length) ∧ final.reg 3 = word width 0 ∧
      (∀ register : Fin 8, register ≠ 2 → register ≠ 3 → register ≠ 5 →
        final.reg register = state.reg register) := by
  intro occurrences
  induction occurrences with
  | nil =>
    intro cursor state position running room cursorFits countFits cursorHeld countHeld
      rankHeld zeroHeld maskHeld stored
    let final : State width 8 := { state.advance with pc := word width done }
    have transition : programStep resident state = some final := by
      rw [fetched resident state entry (.branchZero 3 (word width done)) position (by omega)
        (by simpa [mappedOccurrenceCopyCode] using physical ⟨0, by decide⟩)]
      exact copy_branch_zero state 3 done running countHeld
    have trace := Execution.cons transition (Execution.refl final)
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, max state.liveWords final.liveWords, ?_, ?_, ?_, rfl, rfl, rfl,
      running, ?_, countHeld, ?_⟩
    · simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using trace
    · simp only [live, Nat.max_self, List.length_nil, Nat.add_zero, Nat.le_refl]
    · change state.heap = state.heap ++ ([] : List (Word width)).toArray
      rw [copy_nil_array, Array.append_empty]
    · change state.reg 2 = word width (cursor + ([] : List (MappedOccurrence width)).length)
      simpa only [List.length_nil, Nat.add_zero] using cursorHeld
    · intro register notCursor notCount notTemporary
      rfl
  | cons occurrence rest ih =>
    intro cursor state position running room cursorFits countFits cursorHeld countHeld
      rankHeld zeroHeld maskHeld stored
    obtain ⟨sourceCell, rankCell, originalFits⟩ := stored ⟨0, by simp⟩
    have sourceFirst : state.heap[cursor]? = some (word width occurrence.original) := by
      simpa only [List.getElem_cons_zero, Nat.add_zero] using sourceCell
    have rankFirst : state.heap[rankBase + occurrence.original]? = some occurrence.mapped := by
      simpa only [List.getElem_cons_zero] using rankCell
    have originalFitsFirst : occurrence.original < 2 ^ width := by
      simpa only [List.getElem_cons_zero] using originalFits
    obtain ⟨middle, firstPeak, firstTrace, firstSpace, middleHeap, middleStack,
      middleOutput, middlePC, middleRunning, middleCursor, middleCount, frame⟩ :=
      mapped_occurrence_execution resident entry done cursor (occurrence :: rest).length
        rankBase occurrence.original occurrence.mapped state physical position running codeFits
        (by simp only [List.length_cons] at room; omega) countFits (by simp)
        (by simp only [List.length_cons] at cursorFits; omega) originalFitsFirst
        cursorHeld countHeld rankHeld zeroHeld maskHeld sourceFirst rankFirst
    have middleSize : middle.heap.size = state.heap.size + 1 := by
      rw [middleHeap, Array.size_push]
    have middleLive : middle.liveWords = state.liveWords + 1 := by
      simp only [State.liveWords, middleSize, middleStack, middleOutput]
      omega
    have preserve : ∀ (address : Nat) (value : Word width), state.heap[address]? = some value →
        middle.heap[address]? = some value := by
      intro address value cell
      obtain ⟨valid, actual⟩ := Array.getElem?_eq_some_iff.mp cell
      rw [middleHeap, Array.getElem?_eq_getElem (by simp only [Array.size_push]; omega),
        Array.getElem_push_lt valid, actual]
    have restStored : MappedStreamStored middle.heap (cursor + 1) rankBase rest := by
      intro index
      obtain ⟨sourceOld, rankOld, fitsOld⟩ :=
        stored ⟨index.val + 1, by have := index.isLt; simp only [List.length_cons]; omega⟩
      simp only [List.getElem_cons_succ] at sourceOld rankOld fitsOld
      refine ⟨?_, preserve _ _ rankOld, fitsOld⟩
      have kept := preserve _ _ sourceOld
      simpa only [Nat.add_assoc, Nat.add_comm 1 index.val] using kept
    obtain ⟨final, restPeak, restTrace, restSpace, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalCursor, finalCount, finalFrame⟩ :=
      ih (cursor + 1) middle middlePC middleRunning
        (by simp only [List.length_cons] at room; rw [middleSize]; omega)
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [List.length_cons] at countFits; omega)
        middleCursor (by simpa only [List.length_cons, Nat.add_sub_cancel] using middleCount)
        ((frame 4 (by decide) (by decide) (by decide)).trans rankHeld)
        ((frame 6 (by decide) (by decide) (by decide)).trans zeroHeld)
        ((frame 7 (by decide) (by decide) (by decide)).trans maskHeld) restStored
    refine ⟨final, max firstPeak restPeak, ?_, ?_, ?_, finalStack.trans middleStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, ?_, finalCount, ?_⟩
    · have trace := firstTrace.append restTrace
      convert trace using 1 <;> simp only [List.length_cons] <;> omega
    · rw [max_le_iff]
      constructor <;> simp only [List.length_cons] <;> omega
    · rw [finalHeap, middleHeap]
      rw [List.map_cons]
      have conversion := List.toArray_cons occurrence.mapped (rest.map MappedOccurrence.mapped)
      rw [conversion]
      change (state.heap ++ #[occurrence.mapped]) ++ _ = _
      exact Array.append_assoc
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 rest.length] using finalCursor
    · intro register notCursor notCount notTemporary
      exact (finalFrame register notCursor notCount notTemporary).trans
        (frame register notCursor notCount notTemporary)


def directoryHeap (heap : Array (Word width)) (headSlot tailSlot : Nat)
    (childCursor guardCursor childCount guardCount : Nat) : Array (Word width) :=
  (((heap.push (word width childCursor)).push (word width guardCursor)).setIfInBounds
    headSlot (word width (childCursor + childCount))).setIfInBounds
      tailSlot (word width (guardCursor + guardCount))

theorem directory_heap_source_frame (heap : Array (Word width))
    (headSlot tailSlot childCursor guardCursor childCount guardCount address : Nat)
    (value : Word width) (afterHead : headSlot < address) (afterTail : tailSlot < address)
    (cell : heap[address]? = some value) :
    (directoryHeap heap headSlot tailSlot childCursor guardCursor childCount guardCount)[address]? =
      some value := by
  have first := copy_push_cell heap (word width childCursor) value address cell
  have second := copy_push_cell (heap.push (word width childCursor))
    (word width guardCursor) value address first
  obtain ⟨valid, actual⟩ := Array.getElem?_eq_some_iff.mp second
  unfold directoryHeap
  rw [Array.getElem?_eq_getElem (by simpa only [Array.size_setIfInBounds] using valid)]
  rw [Array.getElem_setIfInBounds_ne (by simpa only [Array.size_setIfInBounds] using valid)
      (show tailSlot ≠ address by omega),
    Array.getElem_setIfInBounds_ne valid (show headSlot ≠ address by omega), actual]

structure DirectorySourceRow where
  old : Nat
  children : Nat
  guards : Nat

def DirectoryRowsStored (heap : Array (Word width)) (nodes H cursor : Nat)
    (rows : List DirectorySourceRow) : Prop :=
  ∀ index : Fin rows.length,
    let row := rows[index.val]
    heap[cursor + index.val]? = some (word width row.old) ∧
    heap[H + 9 + 4 * nodes + 2 * row.old]? = some (word width row.children) ∧
    heap[H + 9 + 4 * nodes + 2 * row.old + 1]? = some (word width row.guards)

def directoryCursorWords (childCursor guardCursor : Nat) : List DirectorySourceRow → List (Word width)
  | [] => []
  | row :: rest => word width childCursor :: word width guardCursor ::
      directoryCursorWords (childCursor + row.children) (guardCursor + row.guards) rest

-- The complete fetched iteration consumes one actual Q cell and two original arity cells.
-- Its two stores update only the scratch cursor cells. The rows sequence is supplied
-- by the already produced Q and the original stored row projection at the consumer.
theorem directory_set_cell (heap : Array (Word width)) (slot address : Nat)
    (stored value : Word width) (different : slot ≠ address)
    (cell : heap[address]? = some value) :
    (heap.setIfInBounds slot stored)[address]? = some value := by
  obtain ⟨valid, actual⟩ := Array.getElem?_eq_some_iff.mp cell
  rw [Array.getElem?_eq_getElem (by simpa only [Array.size_setIfInBounds] using valid),
    Array.getElem_setIfInBounds_ne valid different, actual]

theorem copyRegisters_initial_directory (state : State width 8) (count cursor : Nat)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (zeroHeld : state.reg 6 = word width 0) (maskHeld : state.reg 7 = word width (2 ^ width - 1)) :
    state.reg = copyRegisters (word width count) (word width cursor) (state.reg 2)
      (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (word width (2 ^ width - 1)) := by
  funext register
  fin_cases register <;> simp [copyRegisters, countHeld, cursorHeld, zeroHeld, maskHeld]

theorem directory_row_execution (resident : Program width 8)
    (nodes base entry done H old cursor count childCursor guardCursor childCount guardCount : Nat)
    (state : State width 8)
    (physical : ∀ phase : Fin 32, resident[entry + phase.val]? =
      (typedDirectoryCopyCode width nodes base entry done)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 32 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width)
    (positive : 0 < count) (countFits : count < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (childrenFit : childCursor + childCount < 2 ^ width)
    (guardsFit : guardCursor + guardCount < 2 ^ width)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (zeroHeld : state.reg 6 = word width 0) (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (childCell : state.heap[Controller.Horn.WorklistFIFO.headSlot (n := nodes) base]? =
      some (word width childCursor))
    (guardCell : state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base]? =
      some (word width guardCursor))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (queueCell : state.heap[cursor]? = some (word width old))
    (childCountCell : state.heap[H + 9 + 4 * nodes + 2 * old]? = some (word width childCount))
    (guardCountCell : state.heap[H + 9 + 4 * nodes + 2 * old + 1]? = some (word width guardCount))
    (scratchBelow : Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base < H)
    (queueAfterScratch : Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base < cursor) :
    ∃ final peak, Execution resident state final 32 peak ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = directoryHeap state.heap
        (Controller.Horn.WorklistFIFO.headSlot (n := nodes) base)
        (Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base)
        childCursor guardCursor childCount guardCount ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  let headSlot := Controller.Horn.WorklistFIFO.headSlot (n := nodes) base
  let tailSlot := Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base
  let activeSlot := Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base
  let arity := H + 9 + 4 * nodes + 2 * old
  obtain ⟨lastBound, lastValue⟩ := Array.getElem?_eq_some_iff.mp guardCountCell
  obtain ⟨headBound, headValue⟩ := Array.getElem?_eq_some_iff.mp childCell
  obtain ⟨tailBound, tailValue⟩ := Array.getElem?_eq_some_iff.mp guardCell
  obtain ⟨activeBound, activeValue⟩ := Array.getElem?_eq_some_iff.mp rawCell
  have headTail : headSlot < tailSlot := by
    simp only [headSlot, tailSlot, Controller.Horn.WorklistFIFO.headSlot,
      Controller.Horn.WorklistBucketReady.tailSlot]; omega
  have headActive : headSlot ≠ activeSlot := by
    simp only [headSlot, activeSlot, Controller.Horn.WorklistFIFO.headSlot,
      Controller.Horn.WorklistFIFO.activeSlot]; omega
  have tailActive : tailSlot ≠ activeSlot := by
    simp only [tailSlot, activeSlot, Controller.Horn.WorklistBucketReady.tailSlot,
      Controller.Horn.WorklistFIFO.activeSlot]; omega
  have arityFits : arity + 1 < 2 ^ width := by dsimp only [arity]; omega
  have oldFits : old < 2 ^ width := by dsimp only [arity] at arityFits; omega
  have doubleFits : 2 * old < 2 ^ width := by dsimp only [arity] at arityFits; omega
  have Hfits : H < 2 ^ width := by dsimp only [arity] at arityFits; omega
  have headFits : headSlot < 2 ^ width := by change _ < _ at headBound; omega
  have tailFits : tailSlot < 2 ^ width := by change _ < _ at tailBound; omega
  have activeFits : activeSlot < 2 ^ width := by change _ < _ at activeBound; omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  let s1 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (headSlot)) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (headSlot)) (state.reg 3) (state.reg 4) (word width (childCursor)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (headSlot)) (state.reg 3) (state.reg 4) (word width (childCursor)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (childCursor)), pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (tailSlot)) (state.reg 3) (state.reg 4) (word width (childCursor)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (childCursor)), pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (tailSlot)) (state.reg 3) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (childCursor)), pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (tailSlot)) (state.reg 3) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 7) }
  let s8 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (activeSlot)) (state.reg 3) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 8) }
  let s9 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 9) }
  let s10 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 10) }
  let s11 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 11) }
  let s12 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 12) }
  let s13 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (state.reg 4) (word width (9 + 4 * nodes)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 13) }
  let s14 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (2 * old)) (state.reg 4) (word width (9 + 4 * nodes)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 14) }
  let s15 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (2 * old)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 15) }
  let s16 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (headSlot)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 16) }
  let s17 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (childCursor)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 17) }
  let s18 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (childCursor)) (state.reg 4) (word width (childCursor + childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 18) }
  let s19 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (headSlot)) (state.reg 4) (word width (childCursor + childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCursor))).push (word width (guardCursor)), pc := word width (entry + 19) }
  let s20 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (headSlot)) (state.reg 4) (word width (childCursor + childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount)), pc := word width (entry + 20) }
  let s21 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (1)) (state.reg 4) (word width (childCursor + childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount)), pc := word width (entry + 21) }
  let s22 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (childCursor + childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount)), pc := word width (entry + 22) }
  let s23 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount)), pc := word width (entry + 23) }
  let s24 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (tailSlot)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount)), pc := word width (entry + 24) }
  let s25 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (guardCursor)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount)), pc := word width (entry + 25) }
  let s26 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (guardCursor)) (state.reg 4) (word width (guardCursor + guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount)), pc := word width (entry + 26) }
  let s27 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (tailSlot)) (state.reg 4) (word width (guardCursor + guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount)), pc := word width (entry + 27) }
  let s28 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (tailSlot)) (state.reg 4) (word width (guardCursor + guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount))).setIfInBounds tailSlot (word width (guardCursor + guardCount)), pc := word width (entry + 28) }
  let s29 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCursor + guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount))).setIfInBounds tailSlot (word width (guardCursor + guardCount)), pc := word width (entry + 29) }
  let s30 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor + 1)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCursor + guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount))).setIfInBounds tailSlot (word width (guardCursor + guardCount)), pc := word width (entry + 30) }
  let s31 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCursor + guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount))).setIfInBounds tailSlot (word width (guardCursor + guardCount)), pc := word width (entry + 31) }
  let s32 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCursor + guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount))).setIfInBounds tailSlot (word width (guardCursor + guardCount)), pc := word width (entry) }
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.branchZero 0 (word width done)) position (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨0, by decide⟩)]
    have result := copy_branch_nonzero state 0 done count running positive countFits countHeld
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_initial_directory state count cursor countHeld cursorHeld zeroHeld maskHeld) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s1, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 2 (word width (headSlot))) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨1, by decide⟩)]
    have result := copy_constant_step s1 2 (word width (headSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (headSlot))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s2, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨2, by decide⟩)]
    have result := copy_load_step s2 5 2 (headSlot) (word width (childCursor)) running headFits (by rfl) (by
        change (state.heap)[headSlot]? = some (word width (childCursor))
        have kept0 : state.heap[headSlot]? = some (word width (childCursor)) := by simpa only [arity] using childCell
        exact kept0)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (headSlot)) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (childCursor))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords + 0 := by
    simp only [s3, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨3, by decide⟩)]
    have result := copy_allocate_step s3 5 (word width (childCursor)) running (by simp only [s3, Array.size_push, Array.size_setIfInBounds]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords + 1 := by
    simp only [s4, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.constant 2 (word width (tailSlot))) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨4, by decide⟩)]
    have result := copy_constant_step s4 2 (word width (tailSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (headSlot)) (state.reg 3) (state.reg 4) (word width (childCursor)) (word width (0)) (word width (2 ^ width - 1)) (word width (tailSlot))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords + 1 := by
    simp only [s5, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨5, by decide⟩)]
    have result := copy_load_step s5 5 2 (tailSlot) (word width (guardCursor)) running tailFits (by rfl) (by
        change ((state.heap).push (word width (childCursor)))[tailSlot]? = some (word width (guardCursor))
        have kept0 : state.heap[tailSlot]? = some (word width (guardCursor)) := by simpa only [arity] using guardCell
        have kept1 := copy_push_cell (state.heap) (word width (childCursor)) _ _ kept0
        exact kept1)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (tailSlot)) (state.reg 3) (state.reg 4) (word width (childCursor)) (word width (0)) (word width (2 ^ width - 1)) (word width (guardCursor))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords + 1 := by
    simp only [s6, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨6, by decide⟩)]
    have result := copy_allocate_step s6 5 (word width (guardCursor)) running (by simp only [s6, Array.size_push, Array.size_setIfInBounds]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords + 2 := by
    simp only [s7, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.constant 2 (word width (activeSlot))) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨7, by decide⟩)]
    have result := copy_constant_step s7 2 (word width (activeSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (tailSlot)) (state.reg 3) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1)) (word width (activeSlot))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords + 2 := by
    simp only [s8, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.load 2 2) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨8, by decide⟩)]
    have result := copy_load_step s8 2 2 (activeSlot) (word width (H)) running activeFits (by rfl) (by
        change (((state.heap).push (word width (childCursor))).push (word width (guardCursor)))[activeSlot]? = some (word width (H))
        have kept0 : state.heap[activeSlot]? = some (word width (H)) := by simpa only [arity] using rawCell
        have kept1 := copy_push_cell (state.heap) (word width (childCursor)) _ _ kept0
        have kept2 := copy_push_cell ((state.heap).push (word width (childCursor))) (word width (guardCursor)) _ _ kept1
        exact kept2)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (activeSlot)) (state.reg 3) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1)) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords + 2 := by
    simp only [s9, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.load 3 1) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨9, by decide⟩)]
    have result := copy_load_step s9 3 1 (cursor) (word width (old)) running (by omega) (by rfl) (by
        change (((state.heap).push (word width (childCursor))).push (word width (guardCursor)))[cursor]? = some (word width (old))
        have kept0 : state.heap[cursor]? = some (word width (old)) := by simpa only [arity] using queueCell
        have kept1 := copy_push_cell (state.heap) (word width (childCursor)) _ _ kept0
        have kept2 := copy_push_cell ((state.heap).push (word width (childCursor))) (word width (guardCursor)) _ _ kept1
        exact kept2)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1)) (word width (old))) register
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords + 2 := by
    simp only [s10, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.add 3 3 3) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨10, by decide⟩)]
    have result := copy_add_step s10 3 3 3 (old) (old) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (old) + (old) = (2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1)) (word width (2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s10.advance.pc = word width (entry + 11)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s10
        (entry + 10) (by rfl) (by omega)
    · rfl
  have live11 : s11.liveWords = state.liveWords + 2 := by
    simp only [s11, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t11 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.add 2 2 3) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨11, by decide⟩)]
    have result := copy_add_step s11 2 2 3 (H) (2 * old) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (H) + (2 * old) = (H + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s11.advance.pc = word width (entry + 12)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s11
        (entry + 11) (by rfl) (by omega)
    · rfl
  have live12 : s12.liveWords = state.liveWords + 2 := by
    simp only [s12, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t12 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.constant 5 (word width (9 + 4 * nodes))) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨12, by decide⟩)]
    have result := copy_constant_step s12 5 (word width (9 + 4 * nodes)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (state.reg 4) (word width (guardCursor)) (word width (0)) (word width (2 ^ width - 1)) (word width (9 + 4 * nodes))) register
    · rfl
    · rfl
    · rfl
    · change s12.advance.pc = word width (entry + 13)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s12
        (entry + 12) (by rfl) (by omega)
    · rfl
  have live13 : s13.liveWords = state.liveWords + 2 := by
    simp only [s13, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t13 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨13, by decide⟩)]
    have result := copy_add_step s13 2 2 5 (H + 2 * old) (9 + 4 * nodes) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (H + 2 * old) + (9 + 4 * nodes) = (arity) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (state.reg 4) (word width (9 + 4 * nodes)) (word width (0)) (word width (2 ^ width - 1)) (word width (arity))) register
    · rfl
    · rfl
    · rfl
    · change s13.advance.pc = word width (entry + 14)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s13
        (entry + 13) (by rfl) (by omega)
    · rfl
  have live14 : s14.liveWords = state.liveWords + 2 := by
    simp only [s14, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t14 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 14) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨14, by decide⟩)]
    have result := copy_load_step s14 5 2 (arity) (word width (childCount)) running (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by
        change (((state.heap).push (word width (childCursor))).push (word width (guardCursor)))[arity]? = some (word width (childCount))
        have kept0 : state.heap[arity]? = some (word width (childCount)) := by simpa only [arity] using childCountCell
        have kept1 := copy_push_cell (state.heap) (word width (childCursor)) _ _ kept0
        have kept2 := copy_push_cell ((state.heap).push (word width (childCursor))) (word width (guardCursor)) _ _ kept1
        exact kept2)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (arity)) (word width (2 * old)) (state.reg 4) (word width (9 + 4 * nodes)) (word width (0)) (word width (2 ^ width - 1)) (word width (childCount))) register
    · rfl
    · rfl
    · rfl
    · change s14.advance.pc = word width (entry + 15)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s14
        (entry + 14) (by rfl) (by omega)
    · rfl
  have live15 : s15.liveWords = state.liveWords + 2 := by
    simp only [s15, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t15 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 15) (.constant 3 (word width (headSlot))) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨15, by decide⟩)]
    have result := copy_constant_step s15 3 (word width (headSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (arity)) (word width (2 * old)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (headSlot))) register
    · rfl
    · rfl
    · rfl
    · change s15.advance.pc = word width (entry + 16)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s15
        (entry + 15) (by rfl) (by omega)
    · rfl
  have live16 : s16.liveWords = state.liveWords + 2 := by
    simp only [s16, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t16 : programStep resident s16 = some s17 := by
    rw [fetched resident s16 (entry + 16) (.load 3 3) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨16, by decide⟩)]
    have result := copy_load_step s16 3 3 (headSlot) (word width (childCursor)) running headFits (by rfl) (by
        change (((state.heap).push (word width (childCursor))).push (word width (guardCursor)))[headSlot]? = some (word width (childCursor))
        have kept0 : state.heap[headSlot]? = some (word width (childCursor)) := by simpa only [arity] using childCell
        have kept1 := copy_push_cell (state.heap) (word width (childCursor)) _ _ kept0
        have kept2 := copy_push_cell ((state.heap).push (word width (childCursor))) (word width (guardCursor)) _ _ kept1
        exact kept2)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (arity)) (word width (headSlot)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (childCursor))) register
    · rfl
    · rfl
    · rfl
    · change s16.advance.pc = word width (entry + 17)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s16
        (entry + 16) (by rfl) (by omega)
    · rfl
  have live17 : s17.liveWords = state.liveWords + 2 := by
    simp only [s17, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t17 : programStep resident s17 = some s18 := by
    rw [fetched resident s17 (entry + 17) (.add 5 5 3) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨17, by decide⟩)]
    have result := copy_add_step s17 5 5 3 (childCount) (childCursor) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (childCount) + (childCursor) = (childCursor + childCount) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (arity)) (word width (childCursor)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (childCursor + childCount))) register
    · rfl
    · rfl
    · rfl
    · change s17.advance.pc = word width (entry + 18)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s17
        (entry + 17) (by rfl) (by omega)
    · rfl
  have live18 : s18.liveWords = state.liveWords + 2 := by
    simp only [s18, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t18 : programStep resident s18 = some s19 := by
    rw [fetched resident s18 (entry + 18) (.constant 3 (word width (headSlot))) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨18, by decide⟩)]
    have result := copy_constant_step s18 3 (word width (headSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (arity)) (word width (childCursor)) (state.reg 4) (word width (childCursor + childCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (headSlot))) register
    · rfl
    · rfl
    · rfl
    · change s18.advance.pc = word width (entry + 19)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s18
        (entry + 18) (by rfl) (by omega)
    · rfl
  have live19 : s19.liveWords = state.liveWords + 2 := by
    simp only [s19, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t19 : programStep resident s19 = some s20 := by
    rw [fetched resident s19 (entry + 19) (.store 3 5) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨19, by decide⟩)]
    have result := copy_store_step s19 3 5 headSlot (word width (childCursor + childCount)) running (by simp only [s19, Array.size_push, Array.size_setIfInBounds]; exact Nat.lt_of_lt_of_le headBound (by omega)) headFits (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s19.advance.pc = word width (entry + 20)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s19
        (entry + 19) (by rfl) (by omega)
    · rfl
  have live20 : s20.liveWords = state.liveWords + 2 := by
    simp only [s20, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t20 : programStep resident s20 = some s21 := by
    rw [fetched resident s20 (entry + 20) (.constant 3 (word width (1))) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨20, by decide⟩)]
    have result := copy_constant_step s20 3 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (arity)) (word width (headSlot)) (state.reg 4) (word width (childCursor + childCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s20.advance.pc = word width (entry + 21)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s20
        (entry + 20) (by rfl) (by omega)
    · rfl
  have live21 : s21.liveWords = state.liveWords + 2 := by
    simp only [s21, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t21 : programStep resident s21 = some s22 := by
    rw [fetched resident s21 (entry + 21) (.add 2 2 3) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨21, by decide⟩)]
    have result := copy_add_step s21 2 2 3 (arity) (1) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (arity) + (1) = (arity + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (arity)) (word width (1)) (state.reg 4) (word width (childCursor + childCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (arity + 1))) register
    · rfl
    · rfl
    · rfl
    · change s21.advance.pc = word width (entry + 22)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s21
        (entry + 21) (by rfl) (by omega)
    · rfl
  have live22 : s22.liveWords = state.liveWords + 2 := by
    simp only [s22, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t22 : programStep resident s22 = some s23 := by
    rw [fetched resident s22 (entry + 22) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨22, by decide⟩)]
    have result := copy_load_step s22 5 2 (arity + 1) (word width (guardCount)) running (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by
        change ((((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount)))[arity + 1]? = some (word width (guardCount))
        have kept0 : state.heap[arity + 1]? = some (word width (guardCount)) := by simpa only [arity] using guardCountCell
        have kept1 := copy_push_cell (state.heap) (word width (childCursor)) _ _ kept0
        have kept2 := copy_push_cell ((state.heap).push (word width (childCursor))) (word width (guardCursor)) _ _ kept1
        have kept3 := directory_set_cell (((state.heap).push (word width (childCursor))).push (word width (guardCursor))) headSlot (arity + 1) (word width (childCursor + childCount)) _ (by dsimp only [arity]; change Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base < H at scratchBelow; omega) kept2
        exact kept3)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (childCursor + childCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (guardCount))) register
    · rfl
    · rfl
    · rfl
    · change s22.advance.pc = word width (entry + 23)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s22
        (entry + 22) (by rfl) (by omega)
    · rfl
  have live23 : s23.liveWords = state.liveWords + 2 := by
    simp only [s23, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t23 : programStep resident s23 = some s24 := by
    rw [fetched resident s23 (entry + 23) (.constant 3 (word width (tailSlot))) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨23, by decide⟩)]
    have result := copy_constant_step s23 3 (word width (tailSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (tailSlot))) register
    · rfl
    · rfl
    · rfl
    · change s23.advance.pc = word width (entry + 24)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s23
        (entry + 23) (by rfl) (by omega)
    · rfl
  have live24 : s24.liveWords = state.liveWords + 2 := by
    simp only [s24, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t24 : programStep resident s24 = some s25 := by
    rw [fetched resident s24 (entry + 24) (.load 3 3) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨24, by decide⟩)]
    have result := copy_load_step s24 3 3 (tailSlot) (word width (guardCursor)) running tailFits (by rfl) (by
        change ((((state.heap).push (word width (childCursor))).push (word width (guardCursor))).setIfInBounds headSlot (word width (childCursor + childCount)))[tailSlot]? = some (word width (guardCursor))
        have kept0 : state.heap[tailSlot]? = some (word width (guardCursor)) := by simpa only [arity] using guardCell
        have kept1 := copy_push_cell (state.heap) (word width (childCursor)) _ _ kept0
        have kept2 := copy_push_cell ((state.heap).push (word width (childCursor))) (word width (guardCursor)) _ _ kept1
        have kept3 := directory_set_cell (((state.heap).push (word width (childCursor))).push (word width (guardCursor))) headSlot (tailSlot) (word width (childCursor + childCount)) _ (by omega) kept2
        exact kept3)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (tailSlot)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (guardCursor))) register
    · rfl
    · rfl
    · rfl
    · change s24.advance.pc = word width (entry + 25)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s24
        (entry + 24) (by rfl) (by omega)
    · rfl
  have live25 : s25.liveWords = state.liveWords + 2 := by
    simp only [s25, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t25 : programStep resident s25 = some s26 := by
    rw [fetched resident s25 (entry + 25) (.add 5 5 3) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨25, by decide⟩)]
    have result := copy_add_step s25 5 5 3 (guardCount) (guardCursor) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (guardCount) + (guardCursor) = (guardCursor + guardCount) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (guardCursor)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (guardCursor + guardCount))) register
    · rfl
    · rfl
    · rfl
    · change s25.advance.pc = word width (entry + 26)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s25
        (entry + 25) (by rfl) (by omega)
    · rfl
  have live26 : s26.liveWords = state.liveWords + 2 := by
    simp only [s26, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t26 : programStep resident s26 = some s27 := by
    rw [fetched resident s26 (entry + 26) (.constant 3 (word width (tailSlot))) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨26, by decide⟩)]
    have result := copy_constant_step s26 3 (word width (tailSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (guardCursor)) (state.reg 4) (word width (guardCursor + guardCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (tailSlot))) register
    · rfl
    · rfl
    · rfl
    · change s26.advance.pc = word width (entry + 27)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s26
        (entry + 26) (by rfl) (by omega)
    · rfl
  have live27 : s27.liveWords = state.liveWords + 2 := by
    simp only [s27, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t27 : programStep resident s27 = some s28 := by
    rw [fetched resident s27 (entry + 27) (.store 3 5) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨27, by decide⟩)]
    have result := copy_store_step s27 3 5 tailSlot (word width (guardCursor + guardCount)) running (by simp only [s27, Array.size_push, Array.size_setIfInBounds]; exact Nat.lt_of_lt_of_le tailBound (by omega)) tailFits (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s27.advance.pc = word width (entry + 28)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s27
        (entry + 27) (by rfl) (by omega)
    · rfl
  have live28 : s28.liveWords = state.liveWords + 2 := by
    simp only [s28, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t28 : programStep resident s28 = some s29 := by
    rw [fetched resident s28 (entry + 28) (.constant 3 (word width (1))) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨28, by decide⟩)]
    have result := copy_constant_step s28 3 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (tailSlot)) (state.reg 4) (word width (guardCursor + guardCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s28.advance.pc = word width (entry + 29)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s28
        (entry + 28) (by rfl) (by omega)
    · rfl
  have live29 : s29.liveWords = state.liveWords + 2 := by
    simp only [s29, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t29 : programStep resident s29 = some s30 := by
    rw [fetched resident s29 (entry + 29) (.add 1 1 3) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨29, by decide⟩)]
    have result := copy_add_step s29 1 1 3 (cursor) (1) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (cursor) + (1) = (cursor + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCursor + guardCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (cursor + 1))) register
    · rfl
    · rfl
    · rfl
    · change s29.advance.pc = word width (entry + 30)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s29
        (entry + 29) (by rfl) (by omega)
    · rfl
  have live30 : s30.liveWords = state.liveWords + 2 := by
    simp only [s30, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t30 : programStep resident s30 = some s31 := by
    rw [fetched resident s30 (entry + 30) (.add 0 0 7) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨30, by decide⟩)]
    have result := copy_add_step s30 0 0 7 (count) (2 ^ width - 1) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    rw [marker_word_decrement count positive countFits] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (count)) (word width (cursor + 1)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCursor + guardCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (count - 1))) register
    · rfl
    · rfl
    · rfl
    · change s30.advance.pc = word width (entry + 31)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s30
        (entry + 30) (by rfl) (by omega)
    · rfl
  have live31 : s31.liveWords = state.liveWords + 2 := by
    simp only [s31, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have t31 : programStep resident s31 = some s32 := by
    rw [fetched resident s31 (entry + 31) (.branchZero 6 (word width entry)) (by rfl) (by omega)
      (by simpa [typedDirectoryCopyCode, headSlot, tailSlot, activeSlot] using physical ⟨31, by decide⟩)]
    have result := copy_branch_zero s31 6 entry running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live32 : s32.liveWords = state.liveWords + 2 := by
    simp only [s32, State.liveWords, Array.size_push, Array.size_setIfInBounds] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.cons t16 (Execution.cons t17 (Execution.cons t18 (Execution.cons t19 (Execution.cons t20 (Execution.cons t21 (Execution.cons t22 (Execution.cons t23 (Execution.cons t24 (Execution.cons t25 (Execution.cons t26 (Execution.cons t27 (Execution.cons t28 (Execution.cons t29 (Execution.cons t30 (Execution.cons t31 (Execution.refl s32))))))))))))))))))))))))))))))))
  refine ⟨s32, max state.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords (max s4.liveWords (max s5.liveWords (max s6.liveWords (max s7.liveWords (max s8.liveWords (max s9.liveWords (max s10.liveWords (max s11.liveWords (max s12.liveWords (max s13.liveWords (max s14.liveWords (max s15.liveWords (max s16.liveWords (max s17.liveWords (max s18.liveWords (max s19.liveWords (max s20.liveWords (max s21.liveWords (max s22.liveWords (max s23.liveWords (max s24.liveWords (max s25.liveWords (max s26.liveWords (max s27.liveWords (max s28.liveWords (max s29.liveWords (max s30.liveWords (max s31.liveWords (s32.liveWords)))))))))))))))))))))))))))))))), ?_, ?_, rfl, rfl, rfl, rfl, running, rfl, rfl, rfl, zeroHeld.symm, maskHeld.symm⟩
  · simpa only [Nat.reduceAdd] using trace
  · simp only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, live14, live15, live16, live17, live18, live19, live20, live21, live22, live23, live24, live25, live26, live27, live28, live29, live30, live31, live32, max_le_iff]
    omega

def directoryFoldHeap (heap : Array (Word width)) (headSlot tailSlot : Nat)
    (childCursor guardCursor : Nat) : List DirectorySourceRow → Array (Word width)
  | [] => heap
  | row :: rest => directoryFoldHeap
      (directoryHeap heap headSlot tailSlot childCursor guardCursor row.children row.guards)
      headSlot tailSlot (childCursor + row.children) (guardCursor + row.guards) rest

theorem directory_heap_size (heap : Array (Word width))
    (headSlot tailSlot childCursor guardCursor childCount guardCount : Nat) :
    (directoryHeap heap headSlot tailSlot childCursor guardCursor childCount guardCount).size =
      heap.size + 2 := by
  simp only [directoryHeap, Array.size_setIfInBounds, Array.size_push] <;> omega

theorem directory_heap_cursor_cells (heap : Array (Word width))
    (headSlot tailSlot childCursor guardCursor childCount guardCount : Nat)
    (headValid : headSlot < heap.size) (tailValid : tailSlot < heap.size)
    (different : headSlot ≠ tailSlot) :
    (directoryHeap heap headSlot tailSlot childCursor guardCursor childCount guardCount)[headSlot]? =
      some (word width (childCursor + childCount)) ∧
    (directoryHeap heap headSlot tailSlot childCursor guardCursor childCount guardCount)[tailSlot]? =
      some (word width (guardCursor + guardCount)) := by
  unfold directoryHeap
  constructor
  · rw [Array.getElem?_eq_getElem (by simp only [Array.size_setIfInBounds, Array.size_push]; omega),
      Array.getElem_setIfInBounds_ne (by simp only [Array.size_setIfInBounds, Array.size_push]; omega)
        different.symm,
      Array.getElem_setIfInBounds_self (by simp only [Array.size_setIfInBounds, Array.size_push]; omega)]
  · rw [Array.getElem?_eq_getElem (by simp only [Array.size_setIfInBounds, Array.size_push]; omega),
      Array.getElem_setIfInBounds_self (by simp only [Array.size_setIfInBounds, Array.size_push]; omega)]

/-- Complete original-Q directory pass, with the same two cursor stores at every
fetched iteration. Original arities and Q IDs are preserved across the actual stores. -/
theorem directory_loop_execution (resident : Program width 8)
    (nodes base entry done H childCursor guardCursor : Nat) (rows : List DirectorySourceRow)
    (physical : ∀ phase : Fin 32, resident[entry + phase.val]? =
      (typedDirectoryCopyCode width nodes base entry done)[phase.val]?)
    (codeFits : entry + 32 < 2 ^ width) :
    ∀ (cursor : Nat) (state : State width 8), state.pc = word width entry →
      state.halted = false → state.heap.size + 2 * rows.length < 2 ^ width →
      cursor + rows.length < 2 ^ width → rows.length < 2 ^ width →
      childCursor + (rows.map DirectorySourceRow.children).sum < 2 ^ width →
      guardCursor + (rows.map DirectorySourceRow.guards).sum < 2 ^ width →
      state.reg 0 = word width rows.length → state.reg 1 = word width cursor →
      state.reg 6 = word width 0 → state.reg 7 = word width (2 ^ width - 1) →
      state.heap[Controller.Horn.WorklistFIFO.headSlot (n := nodes) base]? = some (word width childCursor) →
      state.heap[Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base]? = some (word width guardCursor) →
      state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H) →
      Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base < H →
      Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base < cursor →
      DirectoryRowsStored state.heap nodes H cursor rows →
      ∃ final peak, Execution resident state final (32 * rows.length + 1) peak ∧
        peak ≤ state.liveWords + 2 * rows.length ∧
        final.heap = directoryFoldHeap state.heap
          (Controller.Horn.WorklistFIFO.headSlot (n := nodes) base)
          (Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base)
          childCursor guardCursor rows ∧
        final.stack = state.stack ∧ final.output = state.output ∧
        final.pc = word width done ∧ final.halted = false ∧
        final.reg 0 = word width 0 ∧ final.reg 1 = word width (cursor + rows.length) ∧
        final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  induction rows generalizing childCursor guardCursor with
  | nil =>
    intro cursor state position running room cursorFits countFits childFits guardFits
      countHeld cursorHeld zeroHeld maskHeld childCell guardCell rawCell scratchBelow queueAfter stored
    let final : State width 8 := { state.advance with pc := word width done }
    have transition : programStep resident state = some final := by
      rw [fetched resident state entry (.branchZero 0 (word width done)) position (by omega)
        (by simpa [typedDirectoryCopyCode] using physical ⟨0, by decide⟩)]
      exact copy_branch_zero state 0 done running countHeld
    have trace := Execution.cons transition (Execution.refl final)
    refine ⟨final, max state.liveWords final.liveWords, ?_, ?_, rfl, rfl, rfl, rfl,
      running, countHeld, ?_, rfl, rfl, rfl⟩
    · simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using trace
    · change max state.liveWords state.liveWords ≤ state.liveWords + 2 * ([] : List DirectorySourceRow).length
      simp only [max_self, List.length_nil, Nat.mul_zero, Nat.add_zero, Nat.le_refl]
    · change state.reg 1 = word width (cursor + ([] : List DirectorySourceRow).length)
      simpa only [List.length_nil, Nat.add_zero] using cursorHeld
  | cons row rest ih =>
    intro cursor state position running room cursorFits countFits childFits guardFits
      countHeld cursorHeld zeroHeld maskHeld childCell guardCell rawCell scratchBelow queueAfter stored
    obtain ⟨queueFirst, childFirst, guardFirst⟩ := stored ⟨0, by simp⟩
    simp only [List.getElem_cons_zero, Nat.add_zero] at queueFirst childFirst guardFirst
    have childRoom : childCursor + row.children + (rest.map DirectorySourceRow.children).sum < 2 ^ width := by
      simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using childFits
    have guardRoom : guardCursor + row.guards + (rest.map DirectorySourceRow.guards).sum < 2 ^ width := by
      simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using guardFits
    obtain ⟨middle, firstPeak, firstTrace, firstSpace, middleHeap, middleStack,
      middleOutput, middlePC, middleRunning, middleCount, middleCursor, middleRank,
      middleZero, middleMask⟩ := directory_row_execution resident nodes base entry done H row.old
        cursor (row :: rest).length childCursor guardCursor row.children row.guards state
        physical position running codeFits (by simp only [List.length_cons] at room; omega)
        (by simp) countFits (by simp only [List.length_cons] at cursorFits; omega)
        (by omega) (by omega) countHeld cursorHeld zeroHeld maskHeld childCell guardCell
        rawCell queueFirst childFirst guardFirst scratchBelow queueAfter
    let headSlot := Controller.Horn.WorklistFIFO.headSlot (n := nodes) base
    let tailSlot := Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base
    have headTail : headSlot < tailSlot := by
      simp only [headSlot, tailSlot, Controller.Horn.WorklistFIFO.headSlot,
        Controller.Horn.WorklistBucketReady.tailSlot]; omega
    have preserve : ∀ (address : Nat) (value : Word width), tailSlot < address →
        state.heap[address]? = some value → middle.heap[address]? = some value := by
      intro address value after cell
      rw [middleHeap]
      exact directory_heap_source_frame state.heap headSlot tailSlot _ _ _ _ address value (by omega) after cell
    have restStored : DirectoryRowsStored middle.heap nodes H (cursor + 1) rest := by
      intro index
      obtain ⟨queueOld, childOld, guardOld⟩ :=
        stored ⟨index.val + 1, by have := index.isLt; simp only [List.length_cons]; omega⟩
      simp only [List.getElem_cons_succ] at queueOld childOld guardOld
      refine ⟨?_, preserve _ _ (by change _ < _ at scratchBelow; omega) childOld,
        preserve _ _ (by change _ < _ at scratchBelow; omega) guardOld⟩
      have kept := preserve _ _ (by change _ < _ at queueAfter; omega) queueOld
      simpa only [Nat.add_assoc, Nat.add_comm 1 index.val] using kept
    obtain ⟨headValid, headValue⟩ := Array.getElem?_eq_some_iff.mp childCell
    obtain ⟨tailValid, tailValue⟩ := Array.getElem?_eq_some_iff.mp guardCell
    have updatedCells := directory_heap_cursor_cells state.heap headSlot tailSlot
      childCursor guardCursor row.children row.guards headValid tailValid (by omega)
    rw [← middleHeap] at updatedCells
    have middleSize : middle.heap.size = state.heap.size + 2 := by
      rw [middleHeap, directory_heap_size]
    have middleLive : middle.liveWords = state.liveWords + 2 := by
      simp only [State.liveWords, middleSize, middleStack, middleOutput]; omega
    have rawAfter : middle.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H) := by
      apply preserve _ _ _ rawCell
      simp only [tailSlot, Controller.Horn.WorklistBucketReady.tailSlot,
        Controller.Horn.WorklistFIFO.activeSlot]; omega
    obtain ⟨final, restPeak, restTrace, restSpace, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalCount, finalCursor, finalRank, finalZero, finalMask⟩ :=
      ih (childCursor + row.children) (guardCursor + row.guards) (cursor + 1) middle
        middlePC middleRunning (by simp only [List.length_cons] at room; rw [middleSize]; omega)
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [List.length_cons] at countFits; omega) childRoom guardRoom
        (by simpa only [List.length_cons, Nat.add_sub_cancel] using middleCount) middleCursor
        (middleZero.trans zeroHeld) (middleMask.trans maskHeld) updatedCells.1 updatedCells.2
        rawAfter scratchBelow (by omega) restStored
    refine ⟨final, max firstPeak restPeak, ?_, ?_, ?_, finalStack.trans middleStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, finalCount, ?_,
      finalRank.trans middleRank, finalZero.trans middleZero, finalMask.trans middleMask⟩
    · have trace := firstTrace.append restTrace
      convert trace using 1 <;> simp only [List.length_cons] <;> omega
    · rw [max_le_iff]
      constructor <;> simp only [List.length_cons] <;> omega
    · rw [finalHeap, middleHeap]
      rfl
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 rest.length] using finalCursor

theorem directory_fold_size (heap : Array (Word width))
    (headSlot tailSlot childCursor guardCursor : Nat) (rows : List DirectorySourceRow) :
    (directoryFoldHeap heap headSlot tailSlot childCursor guardCursor rows).size =
      heap.size + 2 * rows.length := by
  induction rows generalizing heap childCursor guardCursor with
  | nil => simp only [directoryFoldHeap, List.length_nil, Nat.mul_zero, Nat.add_zero]
  | cons row rest ih =>
    rw [directoryFoldHeap, ih, directory_heap_size]
    simp only [List.length_cons]
    omega

theorem directory_fold_preserves (heap : Array (Word width))
    (headSlot tailSlot childCursor guardCursor : Nat) (rows : List DirectorySourceRow)
    (address : Nat) (value : Word width)
    (headBelow : headSlot < address) (tailBelow : tailSlot < address)
    (cell : heap[address]? = some value) :
    (directoryFoldHeap heap headSlot tailSlot childCursor guardCursor rows)[address]? = some value := by
  induction rows generalizing heap childCursor guardCursor with
  | nil => exact cell
  | cons row rest ih =>
    apply ih
    exact directory_heap_source_frame heap headSlot tailSlot _ _ _ _ address value headBelow tailBelow cell

theorem directory_cursor_words_length (childCursor guardCursor : Nat)
    (rows : List DirectorySourceRow) : (directoryCursorWords (width := width) childCursor guardCursor rows).length =
      2 * rows.length := by
  induction rows generalizing childCursor guardCursor with
  | nil => rfl
  | cons row rest ih =>
    simp only [directoryCursorWords, List.length_cons, ih]
    omega

theorem directory_pair_cells (heap : Array (Word width))
    (headSlot tailSlot childCursor guardCursor childCount guardCount : Nat)
    (headBelow : headSlot < heap.size) (tailBelow : tailSlot < heap.size) :
    (directoryHeap heap headSlot tailSlot childCursor guardCursor childCount guardCount)[heap.size]? =
      some (word width childCursor) ∧
    (directoryHeap heap headSlot tailSlot childCursor guardCursor childCount guardCount)[heap.size + 1]? =
      some (word width guardCursor) := by
  have first0 : (heap.push (word width childCursor))[heap.size]? = some (word width childCursor) :=
    Array.getElem?_push_eq
  have first := copy_push_cell (heap.push (word width childCursor)) (word width guardCursor)
    _ heap.size first0
  have second : ((heap.push (word width childCursor)).push (word width guardCursor))[heap.size + 1]? =
      some (word width guardCursor) := by
    simpa only [Array.size_push] using
      (Array.getElem?_push_eq (xs := heap.push (word width childCursor)) (x := word width guardCursor))
  unfold directoryHeap
  constructor
  · exact directory_set_cell _ tailSlot heap.size _ _ (by omega)
      (directory_set_cell _ headSlot heap.size _ _ (by omega) first)
  · exact directory_set_cell _ tailSlot (heap.size + 1) _ _ (by omega)
      (directory_set_cell _ headSlot (heap.size + 1) _ _ (by omega) second)

/-- Every emitted directory word is read from the actual final shared heap.
The prefix addresses remain the original allocation origin throughout the stores. -/
theorem directory_fold_packet (heap : Array (Word width))
    (headSlot tailSlot childCursor guardCursor : Nat) (rows : List DirectorySourceRow)
    (headBelow : headSlot < heap.size) (tailBelow : tailSlot < heap.size) :
    ∀ index : Fin (directoryCursorWords (width := width) childCursor guardCursor rows).length,
      (directoryFoldHeap heap headSlot tailSlot childCursor guardCursor rows)[heap.size + index.val]? =
        some ((directoryCursorWords childCursor guardCursor rows)[index.val]) := by
  induction rows generalizing heap childCursor guardCursor with
  | nil => intro index; exact Fin.elim0 index
  | cons row rest ih =>
    intro index
    obtain ⟨first, second⟩ := directory_pair_cells heap headSlot tailSlot childCursor guardCursor
      row.children row.guards headBelow tailBelow
    by_cases firstIndex : index.val = 0
    · have kept := directory_fold_preserves
        (directoryHeap heap headSlot tailSlot childCursor guardCursor row.children row.guards)
        headSlot tailSlot (childCursor + row.children) (guardCursor + row.guards) rest heap.size
        (word width childCursor) (by omega) (by omega) first
      simpa only [directoryFoldHeap, directoryCursorWords, firstIndex, Nat.add_zero,
        List.getElem_cons_zero] using kept
    by_cases secondIndex : index.val = 1
    · have kept := directory_fold_preserves
        (directoryHeap heap headSlot tailSlot childCursor guardCursor row.children row.guards)
        headSlot tailSlot (childCursor + row.children) (guardCursor + row.guards) rest (heap.size + 1)
        (word width guardCursor) (by omega) (by omega) second
      simpa only [directoryFoldHeap, directoryCursorWords, secondIndex, List.getElem_cons_succ,
        List.getElem_cons_zero] using kept
    · have restIndex : index.val - 2 <
          (directoryCursorWords (width := width) (childCursor + row.children)
            (guardCursor + row.guards) rest).length := by
        have bound := index.isLt
        simp only [directoryCursorWords, List.length_cons] at bound
        omega
      have kept := ih
        (directoryHeap heap headSlot tailSlot childCursor guardCursor row.children row.guards)
        (childCursor + row.children) (guardCursor + row.guards)
        (by rw [directory_heap_size]; omega) (by rw [directory_heap_size]; omega)
        ⟨index.val - 2, restIndex⟩
      have selected :
          (directoryCursorWords (width := width) childCursor guardCursor (row :: rest))[index.val] =
          (directoryCursorWords (width := width) (childCursor + row.children)
            (guardCursor + row.guards) rest)[index.val - 2] := by
        have selectedOptional :
            (directoryCursorWords (width := width) childCursor guardCursor (row :: rest))[index.val]? =
            (directoryCursorWords (width := width) (childCursor + row.children)
              (guardCursor + row.guards) rest)[index.val - 2]? := by
          have indexEq : index.val = (index.val - 2) + 1 + 1 := by omega
          conv_lhs => rw [indexEq]
          simp only [directoryCursorWords, List.getElem?_cons_succ]
        rw [List.getElem?_eq_getElem index.isLt,
          List.getElem?_eq_getElem restIndex] at selectedOptional
        exact Option.some.inj selectedOptional
      have addressEq :
          (directoryHeap heap headSlot tailSlot childCursor guardCursor row.children row.guards).size +
            (index.val - 2) = heap.size + index.val := by
        rw [directory_heap_size]
        omega
      rw [addressEq] at kept
      change (directoryFoldHeap heap headSlot tailSlot childCursor guardCursor (row :: rest))[heap.size + index.val]? =
        some ((directoryCursorWords (width := width) (childCursor + row.children)
          (guardCursor + row.guards) rest)[index.val - 2]) at kept
      rw [← selected] at kept
      exact kept

theorem directory_setup_execution (resident : Program width 8)
    (nodes children base entry loop rankBase : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 11, resident[entry + phase.val]? =
      (typedDirectorySetupCode width nodes children base loop)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 11 < 2 ^ width) (room : state.heap.size < 2 ^ width)
    (tailValid : Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base < state.heap.size)
    (rankHeld : state.reg 4 = word width rankBase) :
    ∃ final, Execution resident state final 11 state.liveWords ∧
      final.heap = (state.heap.setIfInBounds
        (Controller.Horn.WorklistFIFO.headSlot (n := nodes) base) (word width (5 + 6 * nodes))).setIfInBounds
        (Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base) (word width (5 + 6 * nodes + children)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width loop ∧ final.halted = false ∧
      final.reg 0 = word width nodes ∧
      final.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = word width 0 ∧ final.reg 7 = word width (2 ^ width - 1) := by
  let headSlot := Controller.Horn.WorklistFIFO.headSlot (n := nodes) base
  let tailSlot := Controller.Horn.WorklistBucketReady.tailSlot (n := nodes) base
  have headTail : headSlot < tailSlot := by
    simp only [headSlot, tailSlot, Controller.Horn.WorklistFIFO.headSlot,
      Controller.Horn.WorklistBucketReady.tailSlot]; omega
  have headValid : headSlot < state.heap.size := by omega
  have headFits : headSlot < 2 ^ width := by omega
  have tailFits : tailSlot < 2 ^ width := by omega
  let s1 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes)) (state.reg 6) (state.reg 7)
      heap := state.heap, pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (headSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes)) (state.reg 6) (state.reg 7)
      heap := state.heap, pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (headSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes)) (state.reg 6) (state.reg 7)
      heap := (state.heap).setIfInBounds headSlot (word width (5 + 6 * nodes)), pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (headSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (state.reg 6) (state.reg 7)
      heap := (state.heap).setIfInBounds headSlot (word width (5 + 6 * nodes)), pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (tailSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (state.reg 6) (state.reg 7)
      heap := (state.heap).setIfInBounds headSlot (word width (5 + 6 * nodes)), pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (state.reg 0) (state.reg 1) (word width (tailSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (state.reg 6) (state.reg 7)
      heap := ((state.heap).setIfInBounds headSlot (word width (5 + 6 * nodes))).setIfInBounds tailSlot (word width (5 + 6 * nodes + children)), pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (word width (nodes)) (state.reg 1) (word width (tailSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (state.reg 6) (state.reg 7)
      heap := ((state.heap).setIfInBounds headSlot (word width (5 + 6 * nodes))).setIfInBounds tailSlot (word width (5 + 6 * nodes + children)), pc := word width (entry + 7) }
  let s8 : State width 8 := { state with
      reg := copyRegisters (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (tailSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (state.reg 6) (state.reg 7)
      heap := ((state.heap).setIfInBounds headSlot (word width (5 + 6 * nodes))).setIfInBounds tailSlot (word width (5 + 6 * nodes + children)), pc := word width (entry + 8) }
  let s9 : State width 8 := { state with
      reg := copyRegisters (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (tailSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (word width (0)) (state.reg 7)
      heap := ((state.heap).setIfInBounds headSlot (word width (5 + 6 * nodes))).setIfInBounds tailSlot (word width (5 + 6 * nodes + children)), pc := word width (entry + 9) }
  let s10 : State width 8 := { state with
      reg := copyRegisters (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (tailSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).setIfInBounds headSlot (word width (5 + 6 * nodes))).setIfInBounds tailSlot (word width (5 + 6 * nodes + children)), pc := word width (entry + 10) }
  let s11 : State width 8 := { state with
      reg := copyRegisters (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (tailSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).setIfInBounds headSlot (word width (5 + 6 * nodes))).setIfInBounds tailSlot (word width (5 + 6 * nodes + children)), pc := word width (loop) }
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.constant 5 (word width (5 + 6 * nodes))) position (by omega)
      (by simpa [typedDirectorySetupCode, headSlot, tailSlot] using physical ⟨0, by decide⟩)]
    have result := copy_constant_step state 5 (word width (5 + 6 * nodes)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      change (if register = 5 then word width (5 + 6 * nodes) else state.reg register) = _
      rw [copyRegisters_initial_rank state rankBase rankHeld]
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (word width rankBase) (state.reg 5) (state.reg 6) (state.reg 7) (word width (5 + 6 * nodes))) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords := by
    simp only [s1, State.liveWords, Array.size_setIfInBounds]
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 2 (word width (headSlot))) (by rfl) (by omega)
      (by simpa [typedDirectorySetupCode, headSlot, tailSlot] using physical ⟨1, by decide⟩)]
    have result := copy_constant_step s1 2 (word width (headSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes)) (state.reg 6) (state.reg 7) (word width (headSlot))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords := by
    simp only [s2, State.liveWords, Array.size_setIfInBounds]
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.store 2 5) (by rfl) (by omega)
      (by simpa [typedDirectorySetupCode, headSlot, tailSlot] using physical ⟨2, by decide⟩)]
    have result := copy_store_step s2 2 5 headSlot (word width (5 + 6 * nodes)) running (by simpa only [s2, Array.size_setIfInBounds] using headValid) headFits (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords := by
    simp only [s3, State.liveWords, Array.size_setIfInBounds]
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.constant 5 (word width (5 + 6 * nodes + children))) (by rfl) (by omega)
      (by simpa [typedDirectorySetupCode, headSlot, tailSlot] using physical ⟨3, by decide⟩)]
    have result := copy_constant_step s3 5 (word width (5 + 6 * nodes + children)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (state.reg 0) (state.reg 1) (word width (headSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes)) (state.reg 6) (state.reg 7) (word width (5 + 6 * nodes + children))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords := by
    simp only [s4, State.liveWords, Array.size_setIfInBounds]
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.constant 2 (word width (tailSlot))) (by rfl) (by omega)
      (by simpa [typedDirectorySetupCode, headSlot, tailSlot] using physical ⟨4, by decide⟩)]
    have result := copy_constant_step s4 2 (word width (tailSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (state.reg 0) (state.reg 1) (word width (headSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (state.reg 6) (state.reg 7) (word width (tailSlot))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords := by
    simp only [s5, State.liveWords, Array.size_setIfInBounds]
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.store 2 5) (by rfl) (by omega)
      (by simpa [typedDirectorySetupCode, headSlot, tailSlot] using physical ⟨5, by decide⟩)]
    have result := copy_store_step s5 2 5 tailSlot (word width (5 + 6 * nodes + children)) running (by simpa only [s5, Array.size_setIfInBounds] using tailValid) tailFits (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords := by
    simp only [s6, State.liveWords, Array.size_setIfInBounds]
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 0 (word width (nodes))) (by rfl) (by omega)
      (by simpa [typedDirectorySetupCode, headSlot, tailSlot] using physical ⟨6, by decide⟩)]
    have result := copy_constant_step s6 0 (word width (nodes)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (state.reg 0) (state.reg 1) (word width (tailSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (state.reg 6) (state.reg 7) (word width (nodes))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords := by
    simp only [s7, State.liveWords, Array.size_setIfInBounds]
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.constant 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base))) (by rfl) (by omega)
      (by simpa [typedDirectorySetupCode, headSlot, tailSlot] using physical ⟨7, by decide⟩)]
    have result := copy_constant_step s7 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (nodes)) (state.reg 1) (word width (tailSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (state.reg 6) (state.reg 7) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords := by
    simp only [s8, State.liveWords, Array.size_setIfInBounds]
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.constant 6 (word width (0))) (by rfl) (by omega)
      (by simpa [typedDirectorySetupCode, headSlot, tailSlot] using physical ⟨8, by decide⟩)]
    have result := copy_constant_step s8 6 (word width (0)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update6 (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (tailSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (state.reg 6) (state.reg 7) (word width (0))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords := by
    simp only [s9, State.liveWords, Array.size_setIfInBounds]
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.constant 7 (word width (2 ^ width - 1))) (by rfl) (by omega)
      (by simpa [typedDirectorySetupCode, headSlot, tailSlot] using physical ⟨9, by decide⟩)]
    have result := copy_constant_step s9 7 (word width (2 ^ width - 1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update7 (word width (nodes)) (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)) (word width (tailSlot)) (state.reg 3) (word width rankBase) (word width (5 + 6 * nodes + children)) (word width (0)) (state.reg 7) (word width (2 ^ width - 1))) register
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords := by
    simp only [s10, State.liveWords, Array.size_setIfInBounds]
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.branchZero 6 (word width loop)) (by rfl) (by omega)
      (by simpa [typedDirectorySetupCode, headSlot, tailSlot] using physical ⟨10, by decide⟩)]
    have result := copy_branch_zero s10 6 loop running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live11 : s11.liveWords = state.liveWords := by
    simp only [s11, State.liveWords, Array.size_setIfInBounds]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.refl s11)))))))))))
  refine ⟨s11, ?_, rfl, rfl, rfl, rfl, running, rfl, rfl, rankHeld.symm, rfl, rfl⟩
  simpa only [Nat.reduceAdd, live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, max_self] using trace

/-- Counted arity pass follows the completed directory pass. Its two words
remain original counts; only dependency IDs in later incidence streams use ranks. -/
def typedArityCopyCode (width nodes base entry done : Nat) : Program width 8 :=
  #[.branchZero 0 (word width done),
    .constant 2 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)),
    .load 2 2, .load 3 1, .add 3 3 3, .add 2 2 3,
    .constant 5 (word width (9 + 4 * nodes)), .add 2 2 5,
    .load 5 2, .allocate 5, .constant 3 (word width 1), .add 2 2 3,
    .load 5 2, .allocate 5, .add 1 1 3, .add 0 0 7,
    .branchZero 6 (word width entry)]

def typedCopyRestartCode (width nodes base entry : Nat) : Program width 8 :=
  #[.constant 0 (word width nodes),
    .constant 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)),
    .branchZero 6 (word width entry)]

-- Complete typed packet layout:
-- 5 global words, 2V tag/head words, 2V directories, 2V arities,
-- E ranked original child occurrences, U unchanged original guard occurrences,
-- R ranked original root occurrences, preserving every listed duplicate/order.
-- The resulting size is exactly5+6V+E+U+R; setup/pass restarts are real instructions.

theorem arity_row_execution (resident : Program width 8)
    (nodes base entry done H old cursor count childCount guardCount : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 17, resident[entry + phase.val]? =
      (typedArityCopyCode width nodes base entry done)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 17 < 2 ^ width) (room : state.heap.size + 2 < 2 ^ width)
    (positive : 0 < count) (countFits : count < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (countHeld : state.reg 0 = word width count) (cursorHeld : state.reg 1 = word width cursor)
    (zeroHeld : state.reg 6 = word width 0) (maskHeld : state.reg 7 = word width (2 ^ width - 1))
    (rawCell : state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H))
    (queueCell : state.heap[cursor]? = some (word width old))
    (childCountCell : state.heap[H + 9 + 4 * nodes + 2 * old]? = some (word width childCount))
    (guardCountCell : state.heap[H + 9 + 4 * nodes + 2 * old + 1]? = some (word width guardCount)) :
    ∃ final peak, Execution resident state final 17 peak ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = (state.heap.push (word width childCount)).push (word width guardCount) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width entry ∧ final.halted = false ∧
      final.reg 0 = word width (count - 1) ∧ final.reg 1 = word width (cursor + 1) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  let activeSlot := Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base
  let arity := H + 9 + 4 * nodes + 2 * old
  obtain ⟨lastBound, lastValue⟩ := Array.getElem?_eq_some_iff.mp guardCountCell
  obtain ⟨activeBound, activeValue⟩ := Array.getElem?_eq_some_iff.mp rawCell
  have arityFits : arity + 1 < 2 ^ width := by dsimp only [arity]; omega
  have activeFits : activeSlot < 2 ^ width := by dsimp only [activeSlot]; omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  let s1 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 1) }
  let s2 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (activeSlot)) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 2) }
  let s3 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 3) }
  let s4 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 4) }
  let s5 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 5) }
  let s6 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 6) }
  let s7 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (state.reg 4) (word width (9 + 4 * nodes)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 7) }
  let s8 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (2 * old)) (state.reg 4) (word width (9 + 4 * nodes)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 8) }
  let s9 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (2 * old)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := state.heap, pc := word width (entry + 9) }
  let s10 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (2 * old)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (childCount)), pc := word width (entry + 10) }
  let s11 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity)) (word width (1)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (childCount)), pc := word width (entry + 11) }
  let s12 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (childCount)), pc := word width (entry + 12) }
  let s13 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := (state.heap).push (word width (childCount)), pc := word width (entry + 13) }
  let s14 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCount))).push (word width (guardCount)), pc := word width (entry + 14) }
  let s15 : State width 8 := { state with
      reg := copyRegisters (word width (count)) (word width (cursor + 1)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCount))).push (word width (guardCount)), pc := word width (entry + 15) }
  let s16 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCount))).push (word width (guardCount)), pc := word width (entry + 16) }
  let s17 : State width 8 := { state with
      reg := copyRegisters (word width (count - 1)) (word width (cursor + 1)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1))
      heap := ((state.heap).push (word width (childCount))).push (word width (guardCount)), pc := word width (entry) }
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.branchZero 0 (word width done)) position (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨0, by decide⟩)]
    have result := copy_branch_nonzero state 0 done count running positive countFits countHeld
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_initial_directory state count cursor countHeld cursorHeld zeroHeld maskHeld) register
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) position (by omega)
    · rfl
  have live1 : s1.liveWords = state.liveWords + 0 := by
    simp only [s1, State.liveWords, Array.size_push] <;> omega
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 2 (word width (activeSlot))) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨1, by decide⟩)]
    have result := copy_constant_step s1 2 (word width (activeSlot)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (activeSlot))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords + 0 := by
    simp only [s2, State.liveWords, Array.size_push] <;> omega
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.load 2 2) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨2, by decide⟩)]
    have result := copy_load_step s2 2 2 (activeSlot) (word width (H)) running activeFits (by rfl) (by
        change (state.heap)[activeSlot]? = some (word width (H))
        have kept0 : state.heap[activeSlot]? = some (word width (H)) := by simpa only [arity] using rawCell
        exact kept0)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (activeSlot)) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords + 0 := by
    simp only [s3, State.liveWords, Array.size_push] <;> omega
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.load 3 1) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨3, by decide⟩)]
    have result := copy_load_step s3 3 1 (cursor) (word width (old)) running (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by
        change (state.heap)[cursor]? = some (word width (old))
        have kept0 : state.heap[cursor]? = some (word width (old)) := by simpa only [arity] using queueCell
        exact kept0)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (old))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords + 0 := by
    simp only [s4, State.liveWords, Array.size_push] <;> omega
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.add 3 3 3) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨4, by decide⟩)]
    have result := copy_add_step s4 3 3 3 (old) (old) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (old) + (old) = (2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (H)) (word width (old)) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords + 0 := by
    simp only [s5, State.liveWords, Array.size_push] <;> omega
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.add 2 2 3) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨5, by decide⟩)]
    have result := copy_add_step s5 2 2 3 (H) (2 * old) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (H) + (2 * old) = (H + 2 * old) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H)) (word width (2 * old)) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (H + 2 * old))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords + 0 := by
    simp only [s6, State.liveWords, Array.size_push] <;> omega
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 5 (word width (9 + 4 * nodes))) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨6, by decide⟩)]
    have result := copy_constant_step s6 5 (word width (9 + 4 * nodes)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (9 + 4 * nodes))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords + 0 := by
    simp only [s7, State.liveWords, Array.size_push] <;> omega
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 2 2 5) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨7, by decide⟩)]
    have result := copy_add_step s7 2 2 5 (H + 2 * old) (9 + 4 * nodes) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (H + 2 * old) + (9 + 4 * nodes) = (arity) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (H + 2 * old)) (word width (2 * old)) (state.reg 4) (word width (9 + 4 * nodes)) (word width (0)) (word width (2 ^ width - 1)) (word width (arity))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords + 0 := by
    simp only [s8, State.liveWords, Array.size_push] <;> omega
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨8, by decide⟩)]
    have result := copy_load_step s8 5 2 (arity) (word width (childCount)) running (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by
        change (state.heap)[arity]? = some (word width (childCount))
        have kept0 : state.heap[arity]? = some (word width (childCount)) := by simpa only [arity] using childCountCell
        exact kept0)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (arity)) (word width (2 * old)) (state.reg 4) (word width (9 + 4 * nodes)) (word width (0)) (word width (2 ^ width - 1)) (word width (childCount))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords + 0 := by
    simp only [s9, State.liveWords, Array.size_push] <;> omega
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨9, by decide⟩)]
    have result := copy_allocate_step s9 5 (word width (childCount)) running (by simp only [s9, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords + 1 := by
    simp only [s10, State.liveWords, Array.size_push] <;> omega
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.constant 3 (word width (1))) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨10, by decide⟩)]
    have result := copy_constant_step s10 3 (word width (1)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update3 (word width (count)) (word width (cursor)) (word width (arity)) (word width (2 * old)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (1))) register
    · rfl
    · rfl
    · rfl
    · change s10.advance.pc = word width (entry + 11)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s10
        (entry + 10) (by rfl) (by omega)
    · rfl
  have live11 : s11.liveWords = state.liveWords + 1 := by
    simp only [s11, State.liveWords, Array.size_push] <;> omega
  have t11 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.add 2 2 3) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨11, by decide⟩)]
    have result := copy_add_step s11 2 2 3 (arity) (1) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (arity) + (1) = (arity + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (count)) (word width (cursor)) (word width (arity)) (word width (1)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (arity + 1))) register
    · rfl
    · rfl
    · rfl
    · change s11.advance.pc = word width (entry + 12)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s11
        (entry + 11) (by rfl) (by omega)
    · rfl
  have live12 : s12.liveWords = state.liveWords + 1 := by
    simp only [s12, State.liveWords, Array.size_push] <;> omega
  have t12 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.load 5 2) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨12, by decide⟩)]
    have result := copy_load_step s12 5 2 (arity + 1) (word width (guardCount)) running (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by
        change ((state.heap).push (word width (childCount)))[arity + 1]? = some (word width (guardCount))
        have kept0 : state.heap[arity + 1]? = some (word width (guardCount)) := by simpa only [arity] using guardCountCell
        have kept1 := copy_push_cell (state.heap) (word width (childCount)) _ _ kept0
        exact kept1)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (childCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (guardCount))) register
    · rfl
    · rfl
    · rfl
    · change s12.advance.pc = word width (entry + 13)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s12
        (entry + 12) (by rfl) (by omega)
    · rfl
  have live13 : s13.liveWords = state.liveWords + 1 := by
    simp only [s13, State.liveWords, Array.size_push] <;> omega
  have t13 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.allocate 5) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨13, by decide⟩)]
    have result := copy_allocate_step s13 5 (word width (guardCount)) running (by simp only [s13, Array.size_push]; omega) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s13.advance.pc = word width (entry + 14)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s13
        (entry + 13) (by rfl) (by omega)
    · rfl
  have live14 : s14.liveWords = state.liveWords + 2 := by
    simp only [s14, State.liveWords, Array.size_push] <;> omega
  have t14 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 14) (.add 1 1 3) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨14, by decide⟩)]
    have result := copy_add_step s14 1 1 3 (cursor) (1) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    have scalar : (cursor) + (1) = (cursor + 1) := by omega
    rw [scalar] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (count)) (word width (cursor)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (cursor + 1))) register
    · rfl
    · rfl
    · rfl
    · change s14.advance.pc = word width (entry + 15)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s14
        (entry + 14) (by rfl) (by omega)
    · rfl
  have live15 : s15.liveWords = state.liveWords + 2 := by
    simp only [s15, State.liveWords, Array.size_push] <;> omega
  have t15 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 15) (.add 0 0 7) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨15, by decide⟩)]
    have result := copy_add_step s15 0 0 7 (count) (2 ^ width - 1) running (by dsimp only [arity] at arityFits ⊢; omega) (by dsimp only [arity] at arityFits ⊢; omega) (by rfl) (by rfl)
    rw [marker_word_decrement count positive countFits] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (count)) (word width (cursor + 1)) (word width (arity + 1)) (word width (1)) (state.reg 4) (word width (guardCount)) (word width (0)) (word width (2 ^ width - 1)) (word width (count - 1))) register
    · rfl
    · rfl
    · rfl
    · change s15.advance.pc = word width (entry + 16)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s15
        (entry + 15) (by rfl) (by omega)
    · rfl
  have live16 : s16.liveWords = state.liveWords + 2 := by
    simp only [s16, State.liveWords, Array.size_push] <;> omega
  have t16 : programStep resident s16 = some s17 := by
    rw [fetched resident s16 (entry + 16) (.branchZero 6 (word width entry)) (by rfl) (by omega)
      (by simpa [typedArityCopyCode, activeSlot] using physical ⟨16, by decide⟩)]
    have result := copy_branch_zero s16 6 entry running (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live17 : s17.liveWords = state.liveWords + 2 := by
    simp only [s17, State.liveWords, Array.size_push] <;> omega
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.cons t16 (Execution.refl s17)))))))))))))))))
  refine ⟨s17, max state.liveWords (max s1.liveWords (max s2.liveWords (max s3.liveWords (max s4.liveWords (max s5.liveWords (max s6.liveWords (max s7.liveWords (max s8.liveWords (max s9.liveWords (max s10.liveWords (max s11.liveWords (max s12.liveWords (max s13.liveWords (max s14.liveWords (max s15.liveWords (max s16.liveWords (s17.liveWords))))))))))))))))), ?_, ?_, rfl, rfl, rfl, rfl, running, rfl, rfl, rfl, zeroHeld.symm, maskHeld.symm⟩
  · simpa only [Nat.reduceAdd] using trace
  · simp only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, live14, live15, live16, live17, max_le_iff]
    omega

def copiedArityWords (rows : List DirectorySourceRow) : List (Word width) :=
  rows.flatMap (fun row => [word width row.children, word width row.guards])

/-- The original-Q arity pass emits all count pairs after all directories.
It preserves original occurrence multiplicities and every retained source cell. -/
theorem arity_loop_execution (resident : Program width 8)
    (nodes base entry done H : Nat)
    (physical : ∀ phase : Fin 17, resident[entry + phase.val]? =
      (typedArityCopyCode width nodes base entry done)[phase.val]?)
    (codeFits : entry + 17 < 2 ^ width) :
    ∀ (rows : List DirectorySourceRow) (cursor : Nat) (state : State width 8),
      state.pc = word width entry → state.halted = false →
      state.heap.size + 2 * rows.length < 2 ^ width →
      cursor + rows.length < 2 ^ width → rows.length < 2 ^ width →
      state.reg 0 = word width rows.length → state.reg 1 = word width cursor →
      state.reg 6 = word width 0 → state.reg 7 = word width (2 ^ width - 1) →
      state.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? = some (word width H) →
      DirectoryRowsStored state.heap nodes H cursor rows →
      ∃ final peak, Execution resident state final (17 * rows.length + 1) peak ∧
        peak ≤ state.liveWords + 2 * rows.length ∧
        final.heap = state.heap ++ (copiedArityWords rows).toArray ∧
        final.stack = state.stack ∧ final.output = state.output ∧
        final.pc = word width done ∧ final.halted = false ∧
        final.reg 0 = word width 0 ∧ final.reg 1 = word width (cursor + rows.length) ∧
        final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  intro rows
  induction rows with
  | nil =>
    intro cursor state position running room cursorFits countFits countHeld cursorHeld
      zeroHeld maskHeld rawCell stored
    let final : State width 8 := { state.advance with pc := word width done }
    have transition : programStep resident state = some final := by
      rw [fetched resident state entry (.branchZero 0 (word width done)) position (by omega)
        (by simpa [typedArityCopyCode] using physical ⟨0, by decide⟩)]
      exact copy_branch_zero state 0 done running countHeld
    have trace := Execution.cons transition (Execution.refl final)
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, max state.liveWords final.liveWords, ?_, ?_, ?_, rfl, rfl, rfl,
      running, countHeld, ?_, rfl, rfl, rfl⟩
    · simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using trace
    · simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, live, max_self, Nat.le_refl]
    · change state.heap = state.heap ++ (copiedArityWords []).toArray
      simp only [copiedArityWords, List.flatMap_nil, copy_nil_array, Array.append_empty]
    · change state.reg 1 = word width cursor
      exact cursorHeld
  | cons row rest ih =>
    intro cursor state position running room cursorFits countFits countHeld cursorHeld
      zeroHeld maskHeld rawCell stored
    obtain ⟨queueCell, childCell, guardCell⟩ := stored ⟨0, by simp⟩
    have queueFirst : state.heap[cursor]? = some (word width row.old) := by
      simpa only [List.getElem_cons_zero, Nat.add_zero] using queueCell
    have childFirst : state.heap[H + 9 + 4 * nodes + 2 * row.old]? = some (word width row.children) := by
      simpa only [List.getElem_cons_zero] using childCell
    have guardFirst : state.heap[H + 9 + 4 * nodes + 2 * row.old + 1]? = some (word width row.guards) := by
      simpa only [List.getElem_cons_zero] using guardCell
    obtain ⟨middle, firstPeak, firstTrace, firstSpace, middleHeap,
      middleStack, middleOutput, middlePC, middleRunning, middleCount, middleCursor,
      middleRank, middleZero, middleMask⟩ := arity_row_execution resident nodes base entry done H
        row.old cursor (row :: rest).length row.children row.guards state physical position running
        codeFits (by simp only [List.length_cons] at room; omega) (by simp) countFits
        (by simp only [List.length_cons] at cursorFits; omega)
        countHeld cursorHeld zeroHeld maskHeld rawCell queueFirst childFirst guardFirst
    have middleSize : middle.heap.size = state.heap.size + 2 := by
      rw [middleHeap]
      simp only [Array.size_push] <;> omega
    have middleLive : middle.liveWords = state.liveWords + 2 := by
      simp only [State.liveWords, middleSize, middleStack, middleOutput]
      omega
    have preserve : ∀ (address : Nat) (value : Word width), state.heap[address]? = some value →
        middle.heap[address]? = some value := by
      intro address value cell
      rw [middleHeap]
      exact copied_pair_preserves state.heap _ _ value address cell
    have restStored : DirectoryRowsStored middle.heap nodes H (cursor + 1) rest := by
      intro index
      obtain ⟨queueOld, childOld, guardOld⟩ :=
        stored ⟨index.val + 1, by have := index.isLt; simp only [List.length_cons]; omega⟩
      simp only [List.getElem_cons_succ] at queueOld childOld guardOld
      refine ⟨?_, preserve _ _ childOld, preserve _ _ guardOld⟩
      have kept := preserve _ _ queueOld
      simpa only [Nat.add_assoc, Nat.add_comm 1 index.val] using kept
    obtain ⟨final, restPeak, restTrace, restSpace, finalHeap,
      finalStack, finalOutput, finalPC, finalRunning, finalCount, finalCursor,
      finalRank, finalZero, finalMask⟩ := ih (cursor + 1) middle middlePC middleRunning
        (by simp only [List.length_cons] at room; rw [middleSize]; omega)
        (by simp only [List.length_cons] at cursorFits; omega)
        (by simp only [List.length_cons] at countFits; omega)
        (by simpa only [List.length_cons, Nat.add_sub_cancel] using middleCount)
        middleCursor (middleZero.trans zeroHeld) (middleMask.trans maskHeld)
        (preserve _ _ rawCell) restStored
    refine ⟨final, max firstPeak restPeak, ?_, ?_, ?_, finalStack.trans middleStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, finalCount, ?_,
      finalRank.trans middleRank, finalZero.trans middleZero, finalMask.trans middleMask⟩
    · have trace := firstTrace.append restTrace
      convert trace using 1 <;> simp only [List.length_cons] <;> omega
    · rw [max_le_iff]
      constructor <;> simp only [List.length_cons] <;> omega
    · rw [finalHeap, middleHeap]
      have words : copiedArityWords (row :: rest) =
          word width row.children :: word width row.guards :: copiedArityWords rest := by
        unfold copiedArityWords
        rw [List.flatMap_cons]
        rfl
      rw [words]
      exact copy_pair_array state.heap _ _ _
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 rest.length] using finalCursor

theorem typed_copy_restart_execution (resident : Program width 8)
    (nodes base entry next : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 3, resident[entry + phase.val]? =
      (typedCopyRestartCode width nodes base next)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 3 < 2 ^ width) (zeroHeld : state.reg 6 = word width 0) :
    ∃ final, Execution resident state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width next ∧ final.halted = false ∧
      final.reg 0 = word width nodes ∧
      final.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base) ∧
      final.reg 4 = state.reg 4 ∧ final.reg 6 = state.reg 6 ∧ final.reg 7 = state.reg 7 := by
  let first := state.advance.put 0 (word width nodes)
  let second := first.advance.put 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base))
  let final : State width 8 := { second.advance with pc := word width next }
  have t0 : programStep resident state = some first := by
    rw [fetched resident state entry (.constant 0 (word width nodes)) position (by omega)
      (by simpa [typedCopyRestartCode] using physical ⟨0, by decide⟩)]
    exact copy_constant_step state 0 (word width nodes) running
  have pc1 : first.pc = word width (entry + 1) :=
    referenceAdvancePC state entry position (by omega)
  have t1 : programStep resident first = some second := by
    rw [fetched resident first (entry + 1)
      (.constant 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base))) pc1 (by omega)
      (by simpa [typedCopyRestartCode] using physical ⟨1, by decide⟩)]
    exact copy_constant_step first 1 _ running
  have pc2 : second.pc = word width (entry + 2) := by
    change first.advance.pc = word width (entry + 2)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC first (entry + 1) pc1 (by omega)
  have t2 : programStep resident second = some final := by
    rw [fetched resident second (entry + 2) (.branchZero 6 (word width next)) pc2 (by omega)
      (by simpa [typedCopyRestartCode] using physical ⟨2, by decide⟩)]
    exact copy_branch_zero second 6 next running
      (by simpa [second, first, State.advance, State.put] using zeroHeld)
  have firstLive : first.liveWords = state.liveWords := rfl
  have secondLive : second.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl final)))
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, rfl, rfl, rfl, rfl, rfl⟩
  simpa only [Nat.reduceAdd, firstLive, secondLive, finalLive, max_self] using trace


end Controller.Cost.RawTypedCopy
