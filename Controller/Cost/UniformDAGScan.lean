module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Mathlib.Tactic.FinCases
public import Controller.Cost.UniformDAGConditional

@[expose] public section

/-! One fixed incidence loop reads original identifiers and stored values.
Register one retains the value-table base, register two the accumulator, and
register three the source cursor. The remaining count and temporary accumulator
are saved in charged stack words. No incidence-dependent instructions are built. -/
namespace Controller.Cost.UniformDAGScan
open Controller.Cost.GateProgram

def code (width base : ℕ) (replacement : Bool) : Code width :=
  [.pop 0, .branchZero 0 (word width (base + 18)), .push 0,
   .load 0 3, .add 0 0 1, .load 0 0,
   .branchZero 0 (word width (base + 8)), .constant 2 (boolWord width replacement),
   .constant 0 (word width 1), .add 3 3 0, .pop 0,
   .push 2, .constant 2 (word width (2 ^ width - 1)), .add 0 0 2,
   .pop 2, .push 0, .constant 0 (word width 0), .branchZero 0 (word width base)]
@[simp] theorem code_length : (code width base replacement).length = 18 := rfl

def state (heap : Array (Word width)) (pc : ℕ) (temporary valueBase accumulator cursor : Word width)
    (stack output : List (Word width)) : State width 4 where
  reg := fun register => if register = 0 then temporary else if register = 1 then valueBase
    else if register = 2 then accumulator else cursor
  heap := heap
  stack := stack
  output := output
  pc := word width pc
  halted := false

private theorem decrement (remaining : ℕ) (fits : remaining + 1 < 2 ^ width) :
    word width ((word width (remaining + 1)).val + (word width (2 ^ width - 1)).val) =
      word width remaining := by
  rw [show (word width (remaining + 1)).val = remaining + 1 from Nat.mod_eq_of_lt fits,
    show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from
      Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)]
  have sum : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by
    have := Nat.two_pow_pos width; omega
  rw [sum]
  simp only [word, Nat.add_mod_left]

private theorem fetched (program : Program width 4) (s : State width 4)
    (base : ℕ) (instruction : Instruction width 4)
    (pc : s.pc = word width base) (fits : base < 2 ^ width)
    (entry : program[base]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem fetchedBlock (program : Program width 4) (s : State width 4)
    (base offset : ℕ) (instructions : Code width)
    (pc : s.pc = word width (base + offset)) (fits : base + offset < 2 ^ width)
    (inside : offset < instructions.length) (block : BlockAt program base instructions) :
    programStep program s = (instructions[offset]?).bind (fun instruction => step instruction s) := by
  unfold programStep
  rw [pc, show (word width (base + offset)).val = base + offset from Nat.mod_eq_of_lt fits,
    block offset inside]
  rfl

private theorem chain (program : Program width registers) (history : ℕ → State width registers)
    (count bound : ℕ)
    (transitions : ∀ index < count, programStep program (history index) = some (history (index + 1)))
    (live : ∀ index ≤ count, (history index).liveWords ≤ bound) :
    ∃ peak, Execution program (history 0) (history count) count peak ∧ peak ≤ bound := by
  induction count generalizing history with
  | zero => exact ⟨_, Execution.refl _, live 0 (by omega)⟩
  | succ count ih =>
      obtain ⟨peak, trace, peakBound⟩ := ih (fun index => history (index + 1))
        (fun index inside => transitions (index + 1) (by omega))
        (fun index inside => live (index + 1) (by omega))
      refine ⟨_, ?_, max_le (live 0 (by omega)) peakBound⟩
      simpa [Nat.add_comm] using Execution.cons (transitions 0 (by omega)) trace

/-- Intermediate states describe fetched phases; they are not runtime lists. -/
def phases (heap : Array (Word width)) (base cursor valueBase identifier remaining : ℕ)
    (temporary accumulator : Word width) (value replacement : Bool)
    (suffix output : List (Word width)) : ℕ → State width 4 :=
  let counter := word width (remaining + 1)
  let finalAccumulator := if value then boolWord width replacement else accumulator
  fun phase => match phase with
  | 0 => state heap (base) (temporary) (word width valueBase) (accumulator) (word width (cursor)) (counter :: suffix) output
  | 1 => state heap (base + 1) (counter) (word width valueBase) (accumulator) (word width (cursor)) (suffix) output
  | 2 => state heap (base + 2) (counter) (word width valueBase) (accumulator) (word width (cursor)) (suffix) output
  | 3 => state heap (base + 3) (counter) (word width valueBase) (accumulator) (word width (cursor)) (counter :: suffix) output
  | 4 => state heap (base + 4) (word width identifier) (word width valueBase) (accumulator) (word width (cursor)) (counter :: suffix) output
  | 5 => state heap (base + 5) (word width (valueBase + identifier)) (word width valueBase) (accumulator) (word width (cursor)) (counter :: suffix) output
  | 6 => state heap (base + 6) (boolWord width value) (word width valueBase) (accumulator) (word width (cursor)) (counter :: suffix) output
  | 7 => state heap (base + 7) (boolWord width value) (word width valueBase) (accumulator) (word width (cursor)) (counter :: suffix) output
  | 8 => state heap (base + 8) (boolWord width value) (word width valueBase) (finalAccumulator) (word width (cursor)) (counter :: suffix) output
  | 9 => state heap (base + 9) (word width 1) (word width valueBase) (finalAccumulator) (word width (cursor)) (counter :: suffix) output
  | 10 => state heap (base + 10) (word width 1) (word width valueBase) (finalAccumulator) (word width (cursor + 1)) (counter :: suffix) output
  | 11 => state heap (base + 11) (counter) (word width valueBase) (finalAccumulator) (word width (cursor + 1)) (suffix) output
  | 12 => state heap (base + 12) (counter) (word width valueBase) (finalAccumulator) (word width (cursor + 1)) (finalAccumulator :: suffix) output
  | 13 => state heap (base + 13) (counter) (word width valueBase) (word width (2 ^ width - 1)) (word width (cursor + 1)) (finalAccumulator :: suffix) output
  | 14 => state heap (base + 14) (word width remaining) (word width valueBase) (word width (2 ^ width - 1)) (word width (cursor + 1)) (finalAccumulator :: suffix) output
  | 15 => state heap (base + 15) (word width remaining) (word width valueBase) (finalAccumulator) (word width (cursor + 1)) (suffix) output
  | 16 => state heap (base + 16) (word width remaining) (word width valueBase) (finalAccumulator) (word width (cursor + 1)) (word width remaining :: suffix) output
  | 17 => state heap (base + 17) (word width 0) (word width valueBase) (finalAccumulator) (word width (cursor + 1)) (word width remaining :: suffix) output
  | _ => state heap (base) (word width 0) (word width valueBase) (finalAccumulator) (word width (cursor + 1)) (word width remaining :: suffix) output

def path (value : Bool) (index : ℕ) : ℕ :=
  if value then index else if index ≤ 6 then index else index + 1

/-- A positive remaining count takes eighteen fetched steps for a true value,
seventeen for false. The base survives, the actual cursor advances, and the
saved count decreases with at most one extra temporary live stack word. -/
private theorem read_transitions (program : Program width 4) (heap : Array (Word width))
    (base cursor valueBase identifier remaining : ℕ) (temporary accumulator : Word width)
    (value replacement : Bool) (suffix output : List (Word width))
    (programFits : base + 18 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (valueFits : valueBase + identifier < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (valueBound : valueBase + identifier < heap.size)
    (source : heap[cursor]'cursorBound = word width identifier)
    (stored : heap[valueBase + identifier]'valueBound = boolWord width value)
    (block : BlockAt program base (code width base replacement))
    (index : Fin 6) :
    programStep program (phases heap base cursor valueBase identifier remaining temporary accumulator
        value replacement suffix output (index.val)) =
      some (phases heap base cursor valueBase identifier remaining temporary accumulator
        value replacement suffix output (index.val + 1)) := by
  have vc : (word width (cursor)).val = cursor := Nat.mod_eq_of_lt (by omega)
  have vb : (word width (valueBase)).val = valueBase := Nat.mod_eq_of_lt (by omega)
  have vi : (word width (identifier)).val = identifier := Nat.mod_eq_of_lt (by omega)
  have va : (word width (valueBase + identifier)).val = valueBase + identifier := Nat.mod_eq_of_lt (by omega)
  have vcount : (word width (remaining + 1)).val = remaining + 1 := Nat.mod_eq_of_lt (by omega)
  have vone : (word width (1)).val = 1 := Nat.mod_eq_of_lt (by omega)
  have vzero : (word width (0)).val = 0 := Nat.mod_eq_of_lt (by omega)
  have addressFits (offset : ℕ) (bound : offset ≤ 18) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  have p0 : (word width (base + 0)).val = base + 0 := Nat.mod_eq_of_lt (addressFits 0 (by decide))
  have p1 : (word width (base + 1)).val = base + 1 := Nat.mod_eq_of_lt (addressFits 1 (by decide))
  have p2 : (word width (base + 2)).val = base + 2 := Nat.mod_eq_of_lt (addressFits 2 (by decide))
  have p3 : (word width (base + 3)).val = base + 3 := Nat.mod_eq_of_lt (addressFits 3 (by decide))
  have p4 : (word width (base + 4)).val = base + 4 := Nat.mod_eq_of_lt (addressFits 4 (by decide))
  have p5 : (word width (base + 5)).val = base + 5 := Nat.mod_eq_of_lt (addressFits 5 (by decide))
  have p6 : (word width (base + 6)).val = base + 6 := Nat.mod_eq_of_lt (addressFits 6 (by decide))
  have p7 : (word width (base + 7)).val = base + 7 := Nat.mod_eq_of_lt (addressFits 7 (by decide))
  have p8 : (word width (base + 8)).val = base + 8 := Nat.mod_eq_of_lt (addressFits 8 (by decide))
  have p9 : (word width (base + 9)).val = base + 9 := Nat.mod_eq_of_lt (addressFits 9 (by decide))
  have p10 : (word width (base + 10)).val = base + 10 := Nat.mod_eq_of_lt (addressFits 10 (by decide))
  have p11 : (word width (base + 11)).val = base + 11 := Nat.mod_eq_of_lt (addressFits 11 (by decide))
  have p12 : (word width (base + 12)).val = base + 12 := Nat.mod_eq_of_lt (addressFits 12 (by decide))
  have p13 : (word width (base + 13)).val = base + 13 := Nat.mod_eq_of_lt (addressFits 13 (by decide))
  have p14 : (word width (base + 14)).val = base + 14 := Nat.mod_eq_of_lt (addressFits 14 (by decide))
  have p15 : (word width (base + 15)).val = base + 15 := Nat.mod_eq_of_lt (addressFits 15 (by decide))
  have p16 : (word width (base + 16)).val = base + 16 := Nat.mod_eq_of_lt (addressFits 16 (by decide))
  have p17 : (word width (base + 17)).val = base + 17 := Nat.mod_eq_of_lt (addressFits 17 (by decide))
  have p18 : (word width (base + 18)).val = base + 18 := Nat.mod_eq_of_lt (addressFits 18 (by decide))
  have mc : (cursor) % 2 ^ width = cursor := vc
  have mb : (valueBase) % 2 ^ width = valueBase := vb
  have mi : (identifier) % 2 ^ width = identifier := vi
  have ma : (valueBase + identifier) % 2 ^ width = valueBase + identifier := va
  have mcount : (remaining + 1) % 2 ^ width = remaining + 1 := vcount
  have mone : (1) % 2 ^ width = 1 := vone
  have mzero : (0) % 2 ^ width = 0 := vzero
  have mp0 : (base + 0) % 2 ^ width = base + 0 := p0
  have mp1 : (base + 1) % 2 ^ width = base + 1 := p1
  have mp2 : (base + 2) % 2 ^ width = base + 2 := p2
  have mp3 : (base + 3) % 2 ^ width = base + 3 := p3
  have mp4 : (base + 4) % 2 ^ width = base + 4 := p4
  have mp5 : (base + 5) % 2 ^ width = base + 5 := p5
  have mp6 : (base + 6) % 2 ^ width = base + 6 := p6
  have mp7 : (base + 7) % 2 ^ width = base + 7 := p7
  have mp8 : (base + 8) % 2 ^ width = base + 8 := p8
  have mp9 : (base + 9) % 2 ^ width = base + 9 := p9
  have mp10 : (base + 10) % 2 ^ width = base + 10 := p10
  have mp11 : (base + 11) % 2 ^ width = base + 11 := p11
  have mp12 : (base + 12) % 2 ^ width = base + 12 := p12
  have mp13 : (base + 13) % 2 ^ width = base + 13 := p13
  have mp14 : (base + 14) % 2 ^ width = base + 14 := p14
  have mp15 : (base + 15) % 2 ^ width = base + 15 := p15
  have mp16 : (base + 16) % 2 ^ width = base + 16 := p16
  have mp17 : (base + 17) % 2 ^ width = base + 17 := p17
  have mp18 : (base + 18) % 2 ^ width = base + 18 := p18
  have md : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have wrap : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by
    have one : 1 ≤ 2 ^ width := Nat.succ_le_of_lt (Nat.two_pow_pos width)
    calc
      remaining + 1 + (2 ^ width - 1) = remaining + ((2 ^ width - 1) + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 (2 ^ width - 1)]
      _ = remaining + 2 ^ width := congrArg (fun x => remaining + x) (Nat.sub_add_cancel one)
      _ = 2 ^ width + remaining := Nat.add_comm _ _
  have arithmetic : (remaining + 1 + (2 ^ width - 1)) % 2 ^ width = remaining % 2 ^ width := by
    rw [wrap, Nat.add_mod_left]
  have phaseBound : (index.val) < 18 := by fin_cases index <;> decide
  have position : (phases heap base cursor valueBase identifier remaining temporary accumulator
        value replacement suffix output (index.val)).pc = word width (base + (index.val)) := by
    fin_cases index <;> rfl
  have instructionBound : (index.val) < (code width base replacement).length := by
    simpa only [code_length] using phaseBound
  rw [fetchedBlock program _ base (index.val) (code width base replacement)
    position (addressFits _ (Nat.le_of_lt phaseBound)) instructionBound block]
  fin_cases index
  all_goals simp [phases, path, code, Option.bind, state, step, State.advance, State.put,
    vc, vb, vi, va, vcount, vone, vzero, cursorBound, valueBound, source, stored,
    p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, decrement remaining countFits,
    boolWord, word, mc, mb, mi, ma, mcount, mone, mzero, md, arithmetic, mp0, mp1, mp2, mp3, mp4, mp5, mp6, mp7, mp8, mp9, mp10, mp11, mp12, mp13, mp14, mp15, mp16, mp17, mp18, Nat.add_mod_left, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem update_true_transitions (program : Program width 4) (heap : Array (Word width))
    (base cursor valueBase identifier remaining : ℕ) (temporary accumulator : Word width)
    (replacement : Bool) (suffix output : List (Word width))
    (programFits : base + 18 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (valueFits : valueBase + identifier < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (valueBound : valueBase + identifier < heap.size)
    (source : heap[cursor]'cursorBound = word width identifier)
    (stored : heap[valueBase + identifier]'valueBound = boolWord width true)
    (block : BlockAt program base (code width base replacement))
    (index : Fin 5) :
    programStep program (phases heap base cursor valueBase identifier remaining temporary accumulator
        true replacement suffix output (6 + index.val)) =
      some (phases heap base cursor valueBase identifier remaining temporary accumulator
        true replacement suffix output (6 + (index.val + 1))) := by
  have vc : (word width (cursor)).val = cursor := Nat.mod_eq_of_lt (by omega)
  have vb : (word width (valueBase)).val = valueBase := Nat.mod_eq_of_lt (by omega)
  have vi : (word width (identifier)).val = identifier := Nat.mod_eq_of_lt (by omega)
  have va : (word width (valueBase + identifier)).val = valueBase + identifier := Nat.mod_eq_of_lt (by omega)
  have vcount : (word width (remaining + 1)).val = remaining + 1 := Nat.mod_eq_of_lt (by omega)
  have vone : (word width (1)).val = 1 := Nat.mod_eq_of_lt (by omega)
  have vzero : (word width (0)).val = 0 := Nat.mod_eq_of_lt (by omega)
  have addressFits (offset : ℕ) (bound : offset ≤ 18) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  have p0 : (word width (base + 0)).val = base + 0 := Nat.mod_eq_of_lt (addressFits 0 (by decide))
  have p1 : (word width (base + 1)).val = base + 1 := Nat.mod_eq_of_lt (addressFits 1 (by decide))
  have p2 : (word width (base + 2)).val = base + 2 := Nat.mod_eq_of_lt (addressFits 2 (by decide))
  have p3 : (word width (base + 3)).val = base + 3 := Nat.mod_eq_of_lt (addressFits 3 (by decide))
  have p4 : (word width (base + 4)).val = base + 4 := Nat.mod_eq_of_lt (addressFits 4 (by decide))
  have p5 : (word width (base + 5)).val = base + 5 := Nat.mod_eq_of_lt (addressFits 5 (by decide))
  have p6 : (word width (base + 6)).val = base + 6 := Nat.mod_eq_of_lt (addressFits 6 (by decide))
  have p7 : (word width (base + 7)).val = base + 7 := Nat.mod_eq_of_lt (addressFits 7 (by decide))
  have p8 : (word width (base + 8)).val = base + 8 := Nat.mod_eq_of_lt (addressFits 8 (by decide))
  have p9 : (word width (base + 9)).val = base + 9 := Nat.mod_eq_of_lt (addressFits 9 (by decide))
  have p10 : (word width (base + 10)).val = base + 10 := Nat.mod_eq_of_lt (addressFits 10 (by decide))
  have p11 : (word width (base + 11)).val = base + 11 := Nat.mod_eq_of_lt (addressFits 11 (by decide))
  have p12 : (word width (base + 12)).val = base + 12 := Nat.mod_eq_of_lt (addressFits 12 (by decide))
  have p13 : (word width (base + 13)).val = base + 13 := Nat.mod_eq_of_lt (addressFits 13 (by decide))
  have p14 : (word width (base + 14)).val = base + 14 := Nat.mod_eq_of_lt (addressFits 14 (by decide))
  have p15 : (word width (base + 15)).val = base + 15 := Nat.mod_eq_of_lt (addressFits 15 (by decide))
  have p16 : (word width (base + 16)).val = base + 16 := Nat.mod_eq_of_lt (addressFits 16 (by decide))
  have p17 : (word width (base + 17)).val = base + 17 := Nat.mod_eq_of_lt (addressFits 17 (by decide))
  have p18 : (word width (base + 18)).val = base + 18 := Nat.mod_eq_of_lt (addressFits 18 (by decide))
  have mc : (cursor) % 2 ^ width = cursor := vc
  have mb : (valueBase) % 2 ^ width = valueBase := vb
  have mi : (identifier) % 2 ^ width = identifier := vi
  have ma : (valueBase + identifier) % 2 ^ width = valueBase + identifier := va
  have mcount : (remaining + 1) % 2 ^ width = remaining + 1 := vcount
  have mone : (1) % 2 ^ width = 1 := vone
  have mzero : (0) % 2 ^ width = 0 := vzero
  have mp0 : (base + 0) % 2 ^ width = base + 0 := p0
  have mp1 : (base + 1) % 2 ^ width = base + 1 := p1
  have mp2 : (base + 2) % 2 ^ width = base + 2 := p2
  have mp3 : (base + 3) % 2 ^ width = base + 3 := p3
  have mp4 : (base + 4) % 2 ^ width = base + 4 := p4
  have mp5 : (base + 5) % 2 ^ width = base + 5 := p5
  have mp6 : (base + 6) % 2 ^ width = base + 6 := p6
  have mp7 : (base + 7) % 2 ^ width = base + 7 := p7
  have mp8 : (base + 8) % 2 ^ width = base + 8 := p8
  have mp9 : (base + 9) % 2 ^ width = base + 9 := p9
  have mp10 : (base + 10) % 2 ^ width = base + 10 := p10
  have mp11 : (base + 11) % 2 ^ width = base + 11 := p11
  have mp12 : (base + 12) % 2 ^ width = base + 12 := p12
  have mp13 : (base + 13) % 2 ^ width = base + 13 := p13
  have mp14 : (base + 14) % 2 ^ width = base + 14 := p14
  have mp15 : (base + 15) % 2 ^ width = base + 15 := p15
  have mp16 : (base + 16) % 2 ^ width = base + 16 := p16
  have mp17 : (base + 17) % 2 ^ width = base + 17 := p17
  have mp18 : (base + 18) % 2 ^ width = base + 18 := p18
  have md : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have wrap : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by
    have one : 1 ≤ 2 ^ width := Nat.succ_le_of_lt (Nat.two_pow_pos width)
    calc
      remaining + 1 + (2 ^ width - 1) = remaining + ((2 ^ width - 1) + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 (2 ^ width - 1)]
      _ = remaining + 2 ^ width := congrArg (fun x => remaining + x) (Nat.sub_add_cancel one)
      _ = 2 ^ width + remaining := Nat.add_comm _ _
  have arithmetic : (remaining + 1 + (2 ^ width - 1)) % 2 ^ width = remaining % 2 ^ width := by
    rw [wrap, Nat.add_mod_left]
  have phaseBound : (6 + index.val) < 18 := by fin_cases index <;> decide
  have position : (phases heap base cursor valueBase identifier remaining temporary accumulator
        true replacement suffix output (6 + index.val)).pc = word width (base + (6 + index.val)) := by
    fin_cases index <;> rfl
  have instructionBound : (6 + index.val) < (code width base replacement).length := by
    simpa only [code_length] using phaseBound
  rw [fetchedBlock program _ base (6 + index.val) (code width base replacement)
    position (addressFits _ (Nat.le_of_lt phaseBound)) instructionBound block]
  fin_cases index
  all_goals simp [phases, path, code, Option.bind, state, step, State.advance, State.put,
    vc, vb, vi, va, vcount, vone, vzero, cursorBound, valueBound, source, stored,
    p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, decrement remaining countFits,
    boolWord, word, mc, mb, mi, ma, mcount, mone, mzero, md, arithmetic, mp0, mp1, mp2, mp3, mp4, mp5, mp6, mp7, mp8, mp9, mp10, mp11, mp12, mp13, mp14, mp15, mp16, mp17, mp18, Nat.add_mod_left, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem update_false_transitions (program : Program width 4) (heap : Array (Word width))
    (base cursor valueBase identifier remaining : ℕ) (temporary accumulator : Word width)
    (replacement : Bool) (suffix output : List (Word width))
    (programFits : base + 18 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (valueFits : valueBase + identifier < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (valueBound : valueBase + identifier < heap.size)
    (source : heap[cursor]'cursorBound = word width identifier)
    (stored : heap[valueBase + identifier]'valueBound = boolWord width false)
    (block : BlockAt program base (code width base replacement))
    (index : Fin 4) :
    programStep program (phases heap base cursor valueBase identifier remaining temporary accumulator
        false replacement suffix output (if index.val = 0 then 6 else 7 + index.val)) =
      some (phases heap base cursor valueBase identifier remaining temporary accumulator
        false replacement suffix output (7 + (index.val + 1))) := by
  have vc : (word width (cursor)).val = cursor := Nat.mod_eq_of_lt (by omega)
  have vb : (word width (valueBase)).val = valueBase := Nat.mod_eq_of_lt (by omega)
  have vi : (word width (identifier)).val = identifier := Nat.mod_eq_of_lt (by omega)
  have va : (word width (valueBase + identifier)).val = valueBase + identifier := Nat.mod_eq_of_lt (by omega)
  have vcount : (word width (remaining + 1)).val = remaining + 1 := Nat.mod_eq_of_lt (by omega)
  have vone : (word width (1)).val = 1 := Nat.mod_eq_of_lt (by omega)
  have vzero : (word width (0)).val = 0 := Nat.mod_eq_of_lt (by omega)
  have addressFits (offset : ℕ) (bound : offset ≤ 18) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  have p0 : (word width (base + 0)).val = base + 0 := Nat.mod_eq_of_lt (addressFits 0 (by decide))
  have p1 : (word width (base + 1)).val = base + 1 := Nat.mod_eq_of_lt (addressFits 1 (by decide))
  have p2 : (word width (base + 2)).val = base + 2 := Nat.mod_eq_of_lt (addressFits 2 (by decide))
  have p3 : (word width (base + 3)).val = base + 3 := Nat.mod_eq_of_lt (addressFits 3 (by decide))
  have p4 : (word width (base + 4)).val = base + 4 := Nat.mod_eq_of_lt (addressFits 4 (by decide))
  have p5 : (word width (base + 5)).val = base + 5 := Nat.mod_eq_of_lt (addressFits 5 (by decide))
  have p6 : (word width (base + 6)).val = base + 6 := Nat.mod_eq_of_lt (addressFits 6 (by decide))
  have p7 : (word width (base + 7)).val = base + 7 := Nat.mod_eq_of_lt (addressFits 7 (by decide))
  have p8 : (word width (base + 8)).val = base + 8 := Nat.mod_eq_of_lt (addressFits 8 (by decide))
  have p9 : (word width (base + 9)).val = base + 9 := Nat.mod_eq_of_lt (addressFits 9 (by decide))
  have p10 : (word width (base + 10)).val = base + 10 := Nat.mod_eq_of_lt (addressFits 10 (by decide))
  have p11 : (word width (base + 11)).val = base + 11 := Nat.mod_eq_of_lt (addressFits 11 (by decide))
  have p12 : (word width (base + 12)).val = base + 12 := Nat.mod_eq_of_lt (addressFits 12 (by decide))
  have p13 : (word width (base + 13)).val = base + 13 := Nat.mod_eq_of_lt (addressFits 13 (by decide))
  have p14 : (word width (base + 14)).val = base + 14 := Nat.mod_eq_of_lt (addressFits 14 (by decide))
  have p15 : (word width (base + 15)).val = base + 15 := Nat.mod_eq_of_lt (addressFits 15 (by decide))
  have p16 : (word width (base + 16)).val = base + 16 := Nat.mod_eq_of_lt (addressFits 16 (by decide))
  have p17 : (word width (base + 17)).val = base + 17 := Nat.mod_eq_of_lt (addressFits 17 (by decide))
  have p18 : (word width (base + 18)).val = base + 18 := Nat.mod_eq_of_lt (addressFits 18 (by decide))
  have mc : (cursor) % 2 ^ width = cursor := vc
  have mb : (valueBase) % 2 ^ width = valueBase := vb
  have mi : (identifier) % 2 ^ width = identifier := vi
  have ma : (valueBase + identifier) % 2 ^ width = valueBase + identifier := va
  have mcount : (remaining + 1) % 2 ^ width = remaining + 1 := vcount
  have mone : (1) % 2 ^ width = 1 := vone
  have mzero : (0) % 2 ^ width = 0 := vzero
  have mp0 : (base + 0) % 2 ^ width = base + 0 := p0
  have mp1 : (base + 1) % 2 ^ width = base + 1 := p1
  have mp2 : (base + 2) % 2 ^ width = base + 2 := p2
  have mp3 : (base + 3) % 2 ^ width = base + 3 := p3
  have mp4 : (base + 4) % 2 ^ width = base + 4 := p4
  have mp5 : (base + 5) % 2 ^ width = base + 5 := p5
  have mp6 : (base + 6) % 2 ^ width = base + 6 := p6
  have mp7 : (base + 7) % 2 ^ width = base + 7 := p7
  have mp8 : (base + 8) % 2 ^ width = base + 8 := p8
  have mp9 : (base + 9) % 2 ^ width = base + 9 := p9
  have mp10 : (base + 10) % 2 ^ width = base + 10 := p10
  have mp11 : (base + 11) % 2 ^ width = base + 11 := p11
  have mp12 : (base + 12) % 2 ^ width = base + 12 := p12
  have mp13 : (base + 13) % 2 ^ width = base + 13 := p13
  have mp14 : (base + 14) % 2 ^ width = base + 14 := p14
  have mp15 : (base + 15) % 2 ^ width = base + 15 := p15
  have mp16 : (base + 16) % 2 ^ width = base + 16 := p16
  have mp17 : (base + 17) % 2 ^ width = base + 17 := p17
  have mp18 : (base + 18) % 2 ^ width = base + 18 := p18
  have md : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have wrap : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by
    have one : 1 ≤ 2 ^ width := Nat.succ_le_of_lt (Nat.two_pow_pos width)
    calc
      remaining + 1 + (2 ^ width - 1) = remaining + ((2 ^ width - 1) + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 (2 ^ width - 1)]
      _ = remaining + 2 ^ width := congrArg (fun x => remaining + x) (Nat.sub_add_cancel one)
      _ = 2 ^ width + remaining := Nat.add_comm _ _
  have arithmetic : (remaining + 1 + (2 ^ width - 1)) % 2 ^ width = remaining % 2 ^ width := by
    rw [wrap, Nat.add_mod_left]
  have phaseBound : (if index.val = 0 then 6 else 7 + index.val) < 18 := by fin_cases index <;> decide
  have position : (phases heap base cursor valueBase identifier remaining temporary accumulator
        false replacement suffix output (if index.val = 0 then 6 else 7 + index.val)).pc = word width (base + (if index.val = 0 then 6 else 7 + index.val)) := by
    fin_cases index <;> rfl
  have instructionBound : (if index.val = 0 then 6 else 7 + index.val) < (code width base replacement).length := by
    simpa only [code_length] using phaseBound
  rw [fetchedBlock program _ base (if index.val = 0 then 6 else 7 + index.val) (code width base replacement)
    position (addressFits _ (Nat.le_of_lt phaseBound)) instructionBound block]
  fin_cases index
  all_goals simp [phases, path, code, Option.bind, state, step, State.advance, State.put,
    vc, vb, vi, va, vcount, vone, vzero, cursorBound, valueBound, source, stored,
    p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, decrement remaining countFits,
    boolWord, word, mc, mb, mi, ma, mcount, mone, mzero, md, arithmetic, mp0, mp1, mp2, mp3, mp4, mp5, mp6, mp7, mp8, mp9, mp10, mp11, mp12, mp13, mp14, mp15, mp16, mp17, mp18, Nat.add_mod_left, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem counter_save_transitions (program : Program width 4) (heap : Array (Word width))
    (base cursor valueBase identifier remaining : ℕ) (temporary accumulator : Word width)
    (value replacement : Bool) (suffix output : List (Word width))
    (programFits : base + 18 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (valueFits : valueBase + identifier < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (valueBound : valueBase + identifier < heap.size)
    (source : heap[cursor]'cursorBound = word width identifier)
    (stored : heap[valueBase + identifier]'valueBound = boolWord width value)
    (block : BlockAt program base (code width base replacement))
    (index : Fin 3) :
    programStep program (phases heap base cursor valueBase identifier remaining temporary accumulator
        value replacement suffix output (11 + index.val)) =
      some (phases heap base cursor valueBase identifier remaining temporary accumulator
        value replacement suffix output (11 + (index.val + 1))) := by
  have vc : (word width (cursor)).val = cursor := Nat.mod_eq_of_lt (by omega)
  have vb : (word width (valueBase)).val = valueBase := Nat.mod_eq_of_lt (by omega)
  have vi : (word width (identifier)).val = identifier := Nat.mod_eq_of_lt (by omega)
  have va : (word width (valueBase + identifier)).val = valueBase + identifier := Nat.mod_eq_of_lt (by omega)
  have vcount : (word width (remaining + 1)).val = remaining + 1 := Nat.mod_eq_of_lt (by omega)
  have vone : (word width (1)).val = 1 := Nat.mod_eq_of_lt (by omega)
  have vzero : (word width (0)).val = 0 := Nat.mod_eq_of_lt (by omega)
  have addressFits (offset : ℕ) (bound : offset ≤ 18) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  have p0 : (word width (base + 0)).val = base + 0 := Nat.mod_eq_of_lt (addressFits 0 (by decide))
  have p1 : (word width (base + 1)).val = base + 1 := Nat.mod_eq_of_lt (addressFits 1 (by decide))
  have p2 : (word width (base + 2)).val = base + 2 := Nat.mod_eq_of_lt (addressFits 2 (by decide))
  have p3 : (word width (base + 3)).val = base + 3 := Nat.mod_eq_of_lt (addressFits 3 (by decide))
  have p4 : (word width (base + 4)).val = base + 4 := Nat.mod_eq_of_lt (addressFits 4 (by decide))
  have p5 : (word width (base + 5)).val = base + 5 := Nat.mod_eq_of_lt (addressFits 5 (by decide))
  have p6 : (word width (base + 6)).val = base + 6 := Nat.mod_eq_of_lt (addressFits 6 (by decide))
  have p7 : (word width (base + 7)).val = base + 7 := Nat.mod_eq_of_lt (addressFits 7 (by decide))
  have p8 : (word width (base + 8)).val = base + 8 := Nat.mod_eq_of_lt (addressFits 8 (by decide))
  have p9 : (word width (base + 9)).val = base + 9 := Nat.mod_eq_of_lt (addressFits 9 (by decide))
  have p10 : (word width (base + 10)).val = base + 10 := Nat.mod_eq_of_lt (addressFits 10 (by decide))
  have p11 : (word width (base + 11)).val = base + 11 := Nat.mod_eq_of_lt (addressFits 11 (by decide))
  have p12 : (word width (base + 12)).val = base + 12 := Nat.mod_eq_of_lt (addressFits 12 (by decide))
  have p13 : (word width (base + 13)).val = base + 13 := Nat.mod_eq_of_lt (addressFits 13 (by decide))
  have p14 : (word width (base + 14)).val = base + 14 := Nat.mod_eq_of_lt (addressFits 14 (by decide))
  have p15 : (word width (base + 15)).val = base + 15 := Nat.mod_eq_of_lt (addressFits 15 (by decide))
  have p16 : (word width (base + 16)).val = base + 16 := Nat.mod_eq_of_lt (addressFits 16 (by decide))
  have p17 : (word width (base + 17)).val = base + 17 := Nat.mod_eq_of_lt (addressFits 17 (by decide))
  have p18 : (word width (base + 18)).val = base + 18 := Nat.mod_eq_of_lt (addressFits 18 (by decide))
  have mc : (cursor) % 2 ^ width = cursor := vc
  have mb : (valueBase) % 2 ^ width = valueBase := vb
  have mi : (identifier) % 2 ^ width = identifier := vi
  have ma : (valueBase + identifier) % 2 ^ width = valueBase + identifier := va
  have mcount : (remaining + 1) % 2 ^ width = remaining + 1 := vcount
  have mone : (1) % 2 ^ width = 1 := vone
  have mzero : (0) % 2 ^ width = 0 := vzero
  have mp0 : (base + 0) % 2 ^ width = base + 0 := p0
  have mp1 : (base + 1) % 2 ^ width = base + 1 := p1
  have mp2 : (base + 2) % 2 ^ width = base + 2 := p2
  have mp3 : (base + 3) % 2 ^ width = base + 3 := p3
  have mp4 : (base + 4) % 2 ^ width = base + 4 := p4
  have mp5 : (base + 5) % 2 ^ width = base + 5 := p5
  have mp6 : (base + 6) % 2 ^ width = base + 6 := p6
  have mp7 : (base + 7) % 2 ^ width = base + 7 := p7
  have mp8 : (base + 8) % 2 ^ width = base + 8 := p8
  have mp9 : (base + 9) % 2 ^ width = base + 9 := p9
  have mp10 : (base + 10) % 2 ^ width = base + 10 := p10
  have mp11 : (base + 11) % 2 ^ width = base + 11 := p11
  have mp12 : (base + 12) % 2 ^ width = base + 12 := p12
  have mp13 : (base + 13) % 2 ^ width = base + 13 := p13
  have mp14 : (base + 14) % 2 ^ width = base + 14 := p14
  have mp15 : (base + 15) % 2 ^ width = base + 15 := p15
  have mp16 : (base + 16) % 2 ^ width = base + 16 := p16
  have mp17 : (base + 17) % 2 ^ width = base + 17 := p17
  have mp18 : (base + 18) % 2 ^ width = base + 18 := p18
  have md : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have wrap : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by
    have one : 1 ≤ 2 ^ width := Nat.succ_le_of_lt (Nat.two_pow_pos width)
    calc
      remaining + 1 + (2 ^ width - 1) = remaining + ((2 ^ width - 1) + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 (2 ^ width - 1)]
      _ = remaining + 2 ^ width := congrArg (fun x => remaining + x) (Nat.sub_add_cancel one)
      _ = 2 ^ width + remaining := Nat.add_comm _ _
  have arithmetic : (remaining + 1 + (2 ^ width - 1)) % 2 ^ width = remaining % 2 ^ width := by
    rw [wrap, Nat.add_mod_left]
  have arithmeticAssoc : (remaining + (1 + (2 ^ width - 1))) % 2 ^ width = remaining % 2 ^ width := by
    simpa only [Nat.add_assoc] using arithmetic
  have phaseBound : (11 + index.val) < 18 := by fin_cases index <;> decide
  have position : (phases heap base cursor valueBase identifier remaining temporary accumulator
        value replacement suffix output (11 + index.val)).pc = word width (base + (11 + index.val)) := by
    fin_cases index <;> rfl
  have instructionBound : (11 + index.val) < (code width base replacement).length := by
    simpa only [code_length] using phaseBound
  rw [fetchedBlock program _ base (11 + index.val) (code width base replacement)
    position (addressFits _ (Nat.le_of_lt phaseBound)) instructionBound block]
  fin_cases index
  all_goals simp [phases, path, code, Option.bind, state, step, State.advance, State.put,
    vc, vb, vi, va, vcount, vone, vzero, cursorBound, valueBound, source, stored,
    p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, decrement remaining countFits,
    boolWord, word, mc, mb, mi, ma, mcount, mone, mzero, md, arithmetic, arithmeticAssoc, mp0, mp1, mp2, mp3, mp4, mp5, mp6, mp7, mp8, mp9, mp10, mp11, mp12, mp13, mp14, mp15, mp16, mp17, mp18, Nat.add_mod_left, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem counter_restore_transitions (program : Program width 4) (heap : Array (Word width))
    (base cursor valueBase identifier remaining : ℕ) (temporary accumulator : Word width)
    (value replacement : Bool) (suffix output : List (Word width))
    (programFits : base + 18 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (valueFits : valueBase + identifier < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (valueBound : valueBase + identifier < heap.size)
    (source : heap[cursor]'cursorBound = word width identifier)
    (stored : heap[valueBase + identifier]'valueBound = boolWord width value)
    (block : BlockAt program base (code width base replacement))
    (index : Fin 4) :
    programStep program (phases heap base cursor valueBase identifier remaining temporary accumulator
        value replacement suffix output (14 + index.val)) =
      some (phases heap base cursor valueBase identifier remaining temporary accumulator
        value replacement suffix output (14 + (index.val + 1))) := by
  have vc : (word width (cursor)).val = cursor := Nat.mod_eq_of_lt (by omega)
  have vb : (word width (valueBase)).val = valueBase := Nat.mod_eq_of_lt (by omega)
  have vi : (word width (identifier)).val = identifier := Nat.mod_eq_of_lt (by omega)
  have va : (word width (valueBase + identifier)).val = valueBase + identifier := Nat.mod_eq_of_lt (by omega)
  have vcount : (word width (remaining + 1)).val = remaining + 1 := Nat.mod_eq_of_lt (by omega)
  have vone : (word width (1)).val = 1 := Nat.mod_eq_of_lt (by omega)
  have vzero : (word width (0)).val = 0 := Nat.mod_eq_of_lt (by omega)
  have addressFits (offset : ℕ) (bound : offset ≤ 18) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  have p0 : (word width (base + 0)).val = base + 0 := Nat.mod_eq_of_lt (addressFits 0 (by decide))
  have p1 : (word width (base + 1)).val = base + 1 := Nat.mod_eq_of_lt (addressFits 1 (by decide))
  have p2 : (word width (base + 2)).val = base + 2 := Nat.mod_eq_of_lt (addressFits 2 (by decide))
  have p3 : (word width (base + 3)).val = base + 3 := Nat.mod_eq_of_lt (addressFits 3 (by decide))
  have p4 : (word width (base + 4)).val = base + 4 := Nat.mod_eq_of_lt (addressFits 4 (by decide))
  have p5 : (word width (base + 5)).val = base + 5 := Nat.mod_eq_of_lt (addressFits 5 (by decide))
  have p6 : (word width (base + 6)).val = base + 6 := Nat.mod_eq_of_lt (addressFits 6 (by decide))
  have p7 : (word width (base + 7)).val = base + 7 := Nat.mod_eq_of_lt (addressFits 7 (by decide))
  have p8 : (word width (base + 8)).val = base + 8 := Nat.mod_eq_of_lt (addressFits 8 (by decide))
  have p9 : (word width (base + 9)).val = base + 9 := Nat.mod_eq_of_lt (addressFits 9 (by decide))
  have p10 : (word width (base + 10)).val = base + 10 := Nat.mod_eq_of_lt (addressFits 10 (by decide))
  have p11 : (word width (base + 11)).val = base + 11 := Nat.mod_eq_of_lt (addressFits 11 (by decide))
  have p12 : (word width (base + 12)).val = base + 12 := Nat.mod_eq_of_lt (addressFits 12 (by decide))
  have p13 : (word width (base + 13)).val = base + 13 := Nat.mod_eq_of_lt (addressFits 13 (by decide))
  have p14 : (word width (base + 14)).val = base + 14 := Nat.mod_eq_of_lt (addressFits 14 (by decide))
  have p15 : (word width (base + 15)).val = base + 15 := Nat.mod_eq_of_lt (addressFits 15 (by decide))
  have p16 : (word width (base + 16)).val = base + 16 := Nat.mod_eq_of_lt (addressFits 16 (by decide))
  have p17 : (word width (base + 17)).val = base + 17 := Nat.mod_eq_of_lt (addressFits 17 (by decide))
  have p18 : (word width (base + 18)).val = base + 18 := Nat.mod_eq_of_lt (addressFits 18 (by decide))
  have mc : (cursor) % 2 ^ width = cursor := vc
  have mb : (valueBase) % 2 ^ width = valueBase := vb
  have mi : (identifier) % 2 ^ width = identifier := vi
  have ma : (valueBase + identifier) % 2 ^ width = valueBase + identifier := va
  have mcount : (remaining + 1) % 2 ^ width = remaining + 1 := vcount
  have mone : (1) % 2 ^ width = 1 := vone
  have mzero : (0) % 2 ^ width = 0 := vzero
  have mp0 : (base + 0) % 2 ^ width = base + 0 := p0
  have mp1 : (base + 1) % 2 ^ width = base + 1 := p1
  have mp2 : (base + 2) % 2 ^ width = base + 2 := p2
  have mp3 : (base + 3) % 2 ^ width = base + 3 := p3
  have mp4 : (base + 4) % 2 ^ width = base + 4 := p4
  have mp5 : (base + 5) % 2 ^ width = base + 5 := p5
  have mp6 : (base + 6) % 2 ^ width = base + 6 := p6
  have mp7 : (base + 7) % 2 ^ width = base + 7 := p7
  have mp8 : (base + 8) % 2 ^ width = base + 8 := p8
  have mp9 : (base + 9) % 2 ^ width = base + 9 := p9
  have mp10 : (base + 10) % 2 ^ width = base + 10 := p10
  have mp11 : (base + 11) % 2 ^ width = base + 11 := p11
  have mp12 : (base + 12) % 2 ^ width = base + 12 := p12
  have mp13 : (base + 13) % 2 ^ width = base + 13 := p13
  have mp14 : (base + 14) % 2 ^ width = base + 14 := p14
  have mp15 : (base + 15) % 2 ^ width = base + 15 := p15
  have mp16 : (base + 16) % 2 ^ width = base + 16 := p16
  have mp17 : (base + 17) % 2 ^ width = base + 17 := p17
  have mp18 : (base + 18) % 2 ^ width = base + 18 := p18
  have md : (2 ^ width - 1) % 2 ^ width = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos width) (by decide))
  have wrap : remaining + 1 + (2 ^ width - 1) = 2 ^ width + remaining := by
    have one : 1 ≤ 2 ^ width := Nat.succ_le_of_lt (Nat.two_pow_pos width)
    calc
      remaining + 1 + (2 ^ width - 1) = remaining + ((2 ^ width - 1) + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 (2 ^ width - 1)]
      _ = remaining + 2 ^ width := congrArg (fun x => remaining + x) (Nat.sub_add_cancel one)
      _ = 2 ^ width + remaining := Nat.add_comm _ _
  have arithmetic : (remaining + 1 + (2 ^ width - 1)) % 2 ^ width = remaining % 2 ^ width := by
    rw [wrap, Nat.add_mod_left]
  have arithmeticAssoc : (remaining + (1 + (2 ^ width - 1))) % 2 ^ width = remaining % 2 ^ width := by
    simpa only [Nat.add_assoc] using arithmetic
  have phaseBound : (14 + index.val) < 18 := by fin_cases index <;> decide
  have position : (phases heap base cursor valueBase identifier remaining temporary accumulator
        value replacement suffix output (14 + index.val)).pc = word width (base + (14 + index.val)) := by
    fin_cases index <;> rfl
  have instructionBound : (14 + index.val) < (code width base replacement).length := by
    simpa only [code_length] using phaseBound
  rw [fetchedBlock program _ base (14 + index.val) (code width base replacement)
    position (addressFits _ (Nat.le_of_lt phaseBound)) instructionBound block]
  fin_cases index
  all_goals simp [phases, path, code, Option.bind, state, step, State.advance, State.put,
    vc, vb, vi, va, vcount, vone, vzero, cursorBound, valueBound, source, stored,
    p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, decrement remaining countFits,
    boolWord, word, mc, mb, mi, ma, mcount, mone, mzero, md, arithmetic, arithmeticAssoc, mp0, mp1, mp2, mp3, mp4, mp5, mp6, mp7, mp8, mp9, mp10, mp11, mp12, mp13, mp14, mp15, mp16, mp17, mp18, Nat.add_mod_left, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals try (congr 1; funext register; fin_cases register <;> simp)

private theorem entry_true (program : Program width 4) (heap : Array (Word width))
    (base cursor valueBase identifier remaining : ℕ) (temporary accumulator : Word width)
    (replacement : Bool) (suffix output : List (Word width))
    (programFits : base + 18 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (valueFits : valueBase + identifier < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (valueBound : valueBase + identifier < heap.size)
    (source : heap[cursor]'cursorBound = word width identifier)
    (stored : heap[valueBase + identifier]'valueBound = boolWord width true)
    (block : BlockAt program base (code width base replacement)) :
    ∃ peak, Execution program
      (state heap base temporary (word width valueBase) accumulator (word width cursor)
        (word width (remaining + 1) :: suffix) output)
      (state heap base (word width 0) (word width valueBase)
        (if true then boolWord width replacement else accumulator) (word width (cursor + 1))
        (word width remaining :: suffix) output)
      (if true then 18 else 17) peak ∧
      peak ≤ 7 + heap.size + suffix.length + output.length := by
  have transitions : ∀ index : Fin (if true then 18 else 17),
      programStep program (phases heap base cursor valueBase identifier remaining temporary accumulator
        true replacement suffix output (path true index.val)) =
      some (phases heap base cursor valueBase identifier remaining temporary accumulator
        true replacement suffix output (path true (index.val + 1))) := by
    intro index
    fin_cases index
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨0, by decide⟩
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨1, by decide⟩
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨2, by decide⟩
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨3, by decide⟩
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨4, by decide⟩
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨5, by decide⟩
    · exact update_true_transitions program heap base cursor valueBase identifier remaining temporary accumulator replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨0, by decide⟩
    · exact update_true_transitions program heap base cursor valueBase identifier remaining temporary accumulator replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨1, by decide⟩
    · exact update_true_transitions program heap base cursor valueBase identifier remaining temporary accumulator replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨2, by decide⟩
    · exact update_true_transitions program heap base cursor valueBase identifier remaining temporary accumulator replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨3, by decide⟩
    · exact update_true_transitions program heap base cursor valueBase identifier remaining temporary accumulator replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨4, by decide⟩
    · exact counter_save_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨0, by decide⟩
    · exact counter_save_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨1, by decide⟩
    · exact counter_save_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨2, by decide⟩
    · exact counter_restore_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨0, by decide⟩
    · exact counter_restore_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨1, by decide⟩
    · exact counter_restore_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨2, by decide⟩
    · exact counter_restore_transitions program heap base cursor valueBase identifier remaining temporary accumulator true replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨3, by decide⟩
  obtain ⟨peak, trace, bound⟩ := chain program
    (fun index => phases heap base cursor valueBase identifier remaining temporary accumulator
      true replacement suffix output (path true index)) (if true then 18 else 17)
    (7 + heap.size + suffix.length + output.length)
    (fun index inside => transitions ⟨index, inside⟩)
    (by intro index inside; unfold phases; split <;>
        simp [state, State.liveWords] <;> omega)
  exact ⟨peak, by simpa [phases, path] using trace, bound⟩

private theorem entry_false (program : Program width 4) (heap : Array (Word width))
    (base cursor valueBase identifier remaining : ℕ) (temporary accumulator : Word width)
    (replacement : Bool) (suffix output : List (Word width))
    (programFits : base + 18 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (valueFits : valueBase + identifier < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (valueBound : valueBase + identifier < heap.size)
    (source : heap[cursor]'cursorBound = word width identifier)
    (stored : heap[valueBase + identifier]'valueBound = boolWord width false)
    (block : BlockAt program base (code width base replacement)) :
    ∃ peak, Execution program
      (state heap base temporary (word width valueBase) accumulator (word width cursor)
        (word width (remaining + 1) :: suffix) output)
      (state heap base (word width 0) (word width valueBase)
        (if false then boolWord width replacement else accumulator) (word width (cursor + 1))
        (word width remaining :: suffix) output)
      (if false then 18 else 17) peak ∧
      peak ≤ 7 + heap.size + suffix.length + output.length := by
  have transitions : ∀ index : Fin (if false then 18 else 17),
      programStep program (phases heap base cursor valueBase identifier remaining temporary accumulator
        false replacement suffix output (path false index.val)) =
      some (phases heap base cursor valueBase identifier remaining temporary accumulator
        false replacement suffix output (path false (index.val + 1))) := by
    intro index
    fin_cases index
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨0, by decide⟩
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨1, by decide⟩
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨2, by decide⟩
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨3, by decide⟩
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨4, by decide⟩
    · exact read_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨5, by decide⟩
    · exact update_false_transitions program heap base cursor valueBase identifier remaining temporary accumulator replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨0, by decide⟩
    · exact update_false_transitions program heap base cursor valueBase identifier remaining temporary accumulator replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨1, by decide⟩
    · exact update_false_transitions program heap base cursor valueBase identifier remaining temporary accumulator replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨2, by decide⟩
    · exact update_false_transitions program heap base cursor valueBase identifier remaining temporary accumulator replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨3, by decide⟩
    · exact counter_save_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨0, by decide⟩
    · exact counter_save_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨1, by decide⟩
    · exact counter_save_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨2, by decide⟩
    · exact counter_restore_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨0, by decide⟩
    · exact counter_restore_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨1, by decide⟩
    · exact counter_restore_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨2, by decide⟩
    · exact counter_restore_transitions program heap base cursor valueBase identifier remaining temporary accumulator false replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block ⟨3, by decide⟩
  obtain ⟨peak, trace, bound⟩ := chain program
    (fun index => phases heap base cursor valueBase identifier remaining temporary accumulator
      false replacement suffix output (path false index)) (if false then 18 else 17)
    (7 + heap.size + suffix.length + output.length)
    (fun index inside => transitions ⟨index, inside⟩)
    (by intro index inside; unfold phases; split <;>
        simp [state, State.liveWords] <;> omega)
  exact ⟨peak, by simpa [phases, path] using trace, bound⟩

theorem entry_execution (program : Program width 4) (heap : Array (Word width))
    (base cursor valueBase identifier remaining : ℕ) (temporary accumulator : Word width)
    (value replacement : Bool) (suffix output : List (Word width))
    (programFits : base + 18 < 2 ^ width) (cursorFits : cursor + 1 < 2 ^ width)
    (valueFits : valueBase + identifier < 2 ^ width) (countFits : remaining + 1 < 2 ^ width)
    (cursorBound : cursor < heap.size) (valueBound : valueBase + identifier < heap.size)
    (source : heap[cursor]'cursorBound = word width identifier)
    (stored : heap[valueBase + identifier]'valueBound = boolWord width value)
    (block : BlockAt program base (code width base replacement)) :
    ∃ peak, Execution program
      (state heap base temporary (word width valueBase) accumulator (word width cursor)
        (word width (remaining + 1) :: suffix) output)
      (state heap base (word width 0) (word width valueBase)
        (if value then boolWord width replacement else accumulator) (word width (cursor + 1))
        (word width remaining :: suffix) output)
      (if value then 18 else 17) peak ∧
      peak ≤ 7 + heap.size + suffix.length + output.length := by
  cases value with
  | false =>
      exact entry_false program heap base cursor valueBase identifier remaining temporary accumulator
        replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block
  | true =>
      exact entry_true program heap base cursor valueBase identifier remaining temporary accumulator
        replacement suffix output programFits cursorFits valueFits countFits cursorBound valueBound source stored block

/-- The actual two-instruction exit consumes the saved zero count without
reading an incidence or allocating a result cell. -/
theorem zero_execution (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (temporary valueBase accumulator cursor : Word width)
    (replacement : Bool) (suffix output : List (Word width))
    (programFits : base + 18 < 2 ^ width)
    (block : BlockAt program base (code width base replacement)) :
    Execution program
      (state heap base temporary valueBase accumulator cursor (word width 0 :: suffix) output)
      (state heap (base + 18) (word width 0) valueBase accumulator cursor suffix output)
      2 (6 + heap.size + suffix.length + output.length) := by
  let start := state heap base temporary valueBase accumulator cursor (word width 0 :: suffix) output
  let middle := state heap (base + 1) (word width 0) valueBase accumulator cursor suffix output
  let final := state heap (base + 18) (word width 0) valueBase accumulator cursor suffix output
  have p0 : (word width base).val = base := Nat.mod_eq_of_lt (by omega)
  have p1 : (word width (base + 1)).val = base + 1 := Nat.mod_eq_of_lt (by omega)
  have first : programStep program start = some middle := by
    rw [fetched program start base (.pop 0) rfl (by omega)
      (by simpa [code] using block 0 (by simp [code]))]
    simp [start, middle, state, step, State.advance, State.put, p0]
    all_goals (congr 1; funext register; fin_cases register <;> simp)
  have second : programStep program middle = some final := by
    rw [fetched program middle (base + 1) (.branchZero 0 (word width (base + 18))) rfl (by omega)
      (by simpa [code] using block 1 (by simp [code]))]
    simp [middle, final, state, step, State.advance, p1, word]
  have trace := Execution.cons first (Execution.cons second (Execution.refl final))
  convert trace using 1 <;> simp [start, middle, final, state, State.liveWords] <;> omega

end Controller.Cost.UniformDAGScan
