module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroDictionary
public import Controller.Cost.ForestZeroCone
public import Controller.Cost.ForestZeroModelLift
public import Mathlib.Data.Fintype.Card

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! A channel-support search reads actual reserved dictionary slots with two
countdowns. It stops at the channel bound, the allocated-count bound, or the
first zero slot. Dictionary inversion excludes exhaustion of count+one marked
channels. An unused slot is used only to extend an existing root-zero witness.
-/
namespace Controller.Cost.ForestZeroNonempty
open Controller.Decoder Controller.Decoder.DAG Controller.CNF
open Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary

def code (width base : ℕ) : Code width :=
  [.branchZero 0 (word width (base + 11)), .branchZero 1 (word width (base + 12)),
   .load 3 2, .branchZero 3 (word width (base + 13)),
   .constant 3 (word width (2 ^ width - 1)), .add 0 0 3, .add 1 1 3,
   .constant 3 (word width 1), .add 2 2 3,
   .constant 3 (word width 0), .branchZero 3 (word width base)]

@[simp] theorem code_length : (code width base).length = 11 := rfl

private theorem fetched (program : Program width 4) (state : State width 4)
    (cursor : ℕ) (instruction : Instruction width 4)
    (pc : state.pc = word width cursor) (fits : cursor < 2 ^ width)
    (entry : program[cursor]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [pc, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem advance_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 : ℕ)
    (stack output : List (Word width)) (fits : cursor < 2 ^ width) :
    (atState heap cursor x0 x1 x2 x3 stack output).advance =
      atState heap (cursor + 1) x0 x1 x2 x3 stack output := by
  simp [atState, State.advance, show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem put0_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 0 (word width value) =
      atState heap cursor value x1 x2 x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put3_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 3 (word width value) =
      atState heap cursor x0 x1 x2 value stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put1_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 1 (word width value) =
      atState heap cursor x0 value x2 x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

private theorem put2_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 2 (word width value) =
      atState heap cursor x0 x1 value x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl


/-- Four actual fetched instructions test both positive counters and read one
physical table slot. The continuation records the observed zero outcome. -/
theorem read_execution (program : Program width 4) (heap : Array (Word width))
    (base left right pointer encoded : ℕ) (stack output : List (Word width))
    (leftFits : left + 1 < 2 ^ width) (rightFits : right + 1 < 2 ^ width)
    (pointerFits : pointer < 2 ^ width) (encodedFits : encoded < 2 ^ width)
    (pointerValid : pointer < heap.size) (cell : heap[pointer]? = some (word width encoded))
    (programFits : base + 13 < 2 ^ width) (block : BlockAt program base (code width base)) :
    Execution program (atState heap base (left + 1) (right + 1) pointer 0 stack output)
      (atState heap (if encoded = 0 then base + 13 else base + 4)
        (left + 1) (right + 1) pointer encoded stack output)
      4 (5 + heap.size + stack.length + output.length) := by
  let s0 := atState heap base (left + 1) (right + 1) pointer 0 stack output
  let s1 := atState heap (base + 1) (left + 1) (right + 1) pointer 0 stack output
  let s2 := atState heap (base + 2) (left + 1) (right + 1) pointer 0 stack output
  let s3 := atState heap (base + 3) (left + 1) (right + 1) pointer encoded stack output
  let s4 := atState heap (if encoded = 0 then base + 13 else base + 4)
    (left + 1) (right + 1) pointer encoded stack output
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.branchZero 0 (word width (base + 11))) rfl (by omega)
      (by simpa [code] using block 0 (by simp [code]))]
    change some (if (word width (left + 1)).val = 0 then
      { s0.advance with pc := word width (base + 11) } else s0.advance) = some s1
    rw [show (word width (left + 1)).val = left + 1 from Nat.mod_eq_of_lt leftFits,
      ite_eq_right (by omega), advance_at _ _ _ _ _ _ _ _ (by omega)]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.branchZero 1 (word width (base + 12))) rfl (by omega)
      (by simpa [code] using block 1 (by simp [code]))]
    change some (if (word width (right + 1)).val = 0 then
      { s1.advance with pc := word width (base + 12) } else s1.advance) = some s2
    rw [show (word width (right + 1)).val = right + 1 from Nat.mod_eq_of_lt rightFits,
      ite_eq_right (by omega), advance_at _ _ _ _ _ _ _ _ (by omega)]
  have t2 : programStep program s2 = some s3 := by
    have actual : heap[pointer] = word width encoded := by
      rw [Array.getElem?_eq_getElem pointerValid] at cell
      exact Option.some.inj cell
    rw [fetched program s2 (base + 2) (.load 3 2) rfl (by omega)
      (by simpa [code] using block 2 (by simp [code]))]
    change (if valid : (word width pointer).val < heap.size then
      some (s2.advance.put 3 heap[(word width pointer).val]) else none) = some s3
    rw [show (word width pointer).val = pointer from Nat.mod_eq_of_lt pointerFits,
      dite_eq_left pointerValid, actual, advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.branchZero 3 (word width (base + 13))) rfl (by omega)
      (by simpa [code] using block 3 (by simp [code]))]
    change some (if (word width encoded).val = 0 then
      { s3.advance with pc := word width (base + 13) } else s3.advance) = some s4
    rw [show (word width encoded).val = encoded from Nat.mod_eq_of_lt encodedFits,
      advance_at _ _ _ _ _ _ _ _ (by omega)]
    by_cases zero : encoded = 0 <;> simp only [zero, ite_true, ite_false, s4, atState]
  have firstTrace := Execution.cons t0 (Execution.cons t1 (Execution.refl s2))
  have secondTrace := Execution.cons t2 (Execution.cons t3 (Execution.refl s4))
  convert firstTrace.append secondTrace using 1 <;>
    simp only [s0, s1, s2, s3, s4, atState_liveWords, Nat.max_self]

/-- Seven fetched instructions decrement both counters and advance the table
pointer. The loop resets its scratch register and returns to its own head. -/
theorem update_execution (program : Program width 4) (heap : Array (Word width))
    (base left right pointer encoded : ℕ) (stack output : List (Word width))
    (leftFits : left + 1 < 2 ^ width) (rightFits : right + 1 < 2 ^ width)
    (pointerFits : pointer + 1 < 2 ^ width) (programFits : base + 13 < 2 ^ width)
    (block : BlockAt program base (code width base)) :
    Execution program (atState heap (base + 4) (left + 1) (right + 1) pointer encoded stack output)
      (atState heap base left right (pointer + 1) 0 stack output)
      7 (5 + heap.size + stack.length + output.length) := by
  let mask := 2 ^ width - 1
  let s0 := atState heap (base + 4) (left + 1) (right + 1) pointer encoded stack output
  let s1 := atState heap (base + 5) (left + 1) (right + 1) pointer mask stack output
  let s2 := atState heap (base + 6) left (right + 1) pointer mask stack output
  let s3 := atState heap (base + 7) left right pointer mask stack output
  let s4 := atState heap (base + 8) left right pointer 1 stack output
  let s5 := atState heap (base + 9) left right (pointer + 1) 1 stack output
  let s6 := atState heap (base + 10) left right (pointer + 1) 0 stack output
  let s7 := atState heap base left right (pointer + 1) 0 stack output
  have maskFits : mask < 2 ^ width := by have := Nat.two_pow_pos width; dsimp [mask]; omega
  have maskWord : (word width mask).val = mask := Nat.mod_eq_of_lt maskFits
  have oneWord : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have decrement (value : ℕ) : word width ((value + 1) + mask) = word width value := by
    have same : (value + 1) + mask = value + 2 ^ width := by have := Nat.two_pow_pos width; dsimp [mask]; omega
    apply Fin.ext
    simp only [word, same, Nat.add_mod_right]
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 (base + 4) (.constant 3 (word width mask)) rfl (by omega)
      (by simpa [code, mask] using block 4 (by simp [code]))]
    change some (s0.advance.put 3 (word width mask)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 5) (.add 0 0 3) rfl (by omega)
      (by simpa [code] using block 5 (by simp [code]))]
    change some (s1.advance.put 0 (word width ((word width (left + 1)).val + (word width mask).val))) = some s2
    rw [show (word width (left + 1)).val = left + 1 from Nat.mod_eq_of_lt leftFits,
      maskWord, decrement, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 6) (.add 1 1 3) rfl (by omega)
      (by simpa [code] using block 6 (by simp [code]))]
    change some (s2.advance.put 1 (word width ((word width (right + 1)).val + (word width mask).val))) = some s3
    rw [show (word width (right + 1)).val = right + 1 from Nat.mod_eq_of_lt rightFits,
      maskWord, decrement, advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 7) (.constant 3 (word width 1)) rfl (by omega)
      (by simpa [code] using block 7 (by simp [code]))]
    change some (s3.advance.put 3 (word width 1)) = some s4
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 8) (.add 2 2 3) rfl (by omega)
      (by simpa [code] using block 8 (by simp [code]))]
    change some (s4.advance.put 2 (word width ((word width pointer).val + (word width 1).val))) = some s5
    rw [show (word width pointer).val = pointer from Nat.mod_eq_of_lt (by omega),
      oneWord, advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (base + 9) (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [code] using block 9 (by simp [code]))]
    change some (s5.advance.put 3 (word width 0)) = some s6
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (base + 10) (.branchZero 3 (word width base)) rfl (by omega)
      (by simpa [code] using block 10 (by simp [code]))]
    change some (if (word width 0).val = 0 then { s6.advance with pc := word width base } else s6.advance) = some s7
    rw [show (word width 0).val = 0 from Nat.zero_mod _, ite_eq_left rfl,
      advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  have firstTrace := Execution.cons t0 (Execution.cons t1 (Execution.refl s2))
  have middleTrace := Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.refl s5)))
  have lastTrace := Execution.cons t5 (Execution.cons t6 (Execution.refl s7))
  convert (firstTrace.append middleTrace).append lastTrace using 1 <;>
    simp only [s0, s1, s2, s3, s4, s5, s6, s7, atState_liveWords, Nat.max_self]

inductive Reason where
  | covered | exhausted | unused
  deriving DecidableEq

structure Result where
  marked : ℕ
  reason : Reason
  deriving DecidableEq

def Result.bump (result : Result) : Result := ⟨result.marked + 1, result.reason⟩

def slotAt (state : Dictionary ambient) (coordinate : ℕ) : ℕ :=
  if valid : coordinate < ambient then state.slots[coordinate] else 0

def search (state : Dictionary ambient) : ℕ → ℕ → ℕ → Result
  | 0, 0, _ => ⟨0, .covered⟩
  | 0, _ + 1, _ => ⟨0, .exhausted⟩
  | _ + 1, 0, _ => ⟨0, .covered⟩
  | budget + 1, channels + 1, offset =>
      if slotAt state offset = 0 then ⟨0, .unused⟩
      else (search state budget channels (offset + 1)).bump

def exitOffset : Reason → ℕ | .covered => 11 | .exhausted => 12 | .unused => 13

def exitTicks : Reason → ℕ | .covered => 1 | .exhausted => 2 | .unused => 4

/-- Every completed nonzero read consumes one unit of each countdown. -/
theorem search_bounds (state : Dictionary ambient) (budget channels offset : ℕ) :
    (search state budget channels offset).marked ≤ budget ∧
      (search state budget channels offset).marked ≤ channels := by
  induction budget generalizing channels offset with
  | zero => cases channels <;> simp [search]
  | succ budget ih =>
      cases channels with
      | zero => simp [search]
      | succ channels =>
          by_cases unused : slotAt state offset = 0
          · simp [search, unused]
          · have prior := ih channels (offset + 1)
            simp only [search, ite_eq_right unused, Result.bump]
            omega

theorem search_prefix (state : Dictionary ambient) (budget channels offset : ℕ) :
    ∀ index < (search state budget channels offset).marked,
      slotAt state (offset + index) ≠ 0 := by
  induction budget generalizing channels offset with
  | zero => cases channels <;> simp [search]
  | succ budget ih =>
      cases channels with
      | zero => simp [search]
      | succ channels =>
          by_cases unused : slotAt state offset = 0
          · simp [search, unused]
          · simp only [search, ite_eq_right unused, Result.bump]
            intro index bound
            cases index with
            | zero => simpa only [Nat.add_zero] using unused
            | succ index =>
                have retained := ih channels (offset + 1) index (by omega)
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using retained

theorem search_stop (state : Dictionary ambient) (budget channels offset : ℕ) :
    match (search state budget channels offset).reason with
    | .covered => (search state budget channels offset).marked = channels
    | .exhausted => (search state budget channels offset).marked = budget ∧ budget < channels
    | .unused => slotAt state (offset + (search state budget channels offset).marked) = 0 ∧
        (search state budget channels offset).marked < channels ∧
        (search state budget channels offset).marked < budget := by
  induction budget generalizing channels offset with
  | zero => cases channels <;> simp [search]
  | succ budget ih =>
      cases channels with
      | zero => simp [search]
      | succ channels =>
          by_cases unused : slotAt state offset = 0
          · simp [search, unused]
          · have prior := ih channels (offset + 1)
            simp only [search, ite_eq_right unused, Result.bump]
            cases reason : (search state budget channels (offset + 1)).reason <;>
              simp only [reason] at prior ⊢
            · omega
            · omega
            · exact ⟨by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using prior.1,
                by omega, by omega⟩

/-- Inversion derives the budget from distinct actual allocator slots. -/
theorem marked_bound (state : Dictionary ambient) (coherent : Coherent state)
    (count : ℕ) (within : count ≤ ambient) (marked : ∀ index < count, slotAt state index ≠ 0) :
    count ≤ state.coordinates.size := by
  let allocated : Fin count → Fin state.coordinates.size := fun index =>
    ⟨state.slots[index.val] - 1, by
      have sourceBound : index.val < ambient := lt_of_lt_of_le index.isLt within
      have nonzero : state.slots[index.val] ≠ 0 := by
        simpa only [slotAt, dite_eq_left sourceBound] using marked index.val index.isLt
      have bounded : state.slots[index.val] ≤ state.coordinates.size :=
        encoded_bound state coherent ⟨index.val, sourceBound⟩
      omega⟩
  have injective : Function.Injective allocated := by
    intro left right equal
    have leftBound : left.val < ambient := lt_of_lt_of_le left.isLt within
    have rightBound : right.val < ambient := lt_of_lt_of_le right.isLt within
    have leftNonzero : state.slots[left.val] ≠ 0 := by
      simpa only [slotAt, dite_eq_left leftBound] using marked left.val left.isLt
    have rightNonzero : state.slots[right.val] ≠ 0 := by
      simpa only [slotAt, dite_eq_left rightBound] using marked right.val right.isLt
    have indices : state.slots[left.val] - 1 = state.slots[right.val] - 1 := congrArg Fin.val equal
    have leftEncoded : state.slots[left.val] = (state.slots[left.val] - 1) + 1 := by omega
    have rightEncoded : state.slots[right.val] = (state.slots[right.val] - 1) + 1 := by omega
    have leftPresent := (coherent ⟨left.val, leftBound⟩ (state.slots[left.val] - 1)).mp leftEncoded
    have rightPresent := (coherent ⟨right.val, rightBound⟩ (state.slots[right.val] - 1)).mp rightEncoded
    rw [indices] at leftPresent
    have same : (⟨left.val, leftBound⟩ : Fin ambient) = ⟨right.val, rightBound⟩ :=
      Option.some.inj (leftPresent.symm.trans rightPresent)
    apply Fin.ext
    exact congrArg (fun coordinate : Fin ambient => coordinate.val) same
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective allocated injective

/-- Exhaustion is impossible for the real count-plus-one budget. -/
theorem search_not_exhausted (state : Dictionary ambient) (coherent : Coherent state)
    (channels : ℕ) (within : channels ≤ ambient) :
    (search state (state.coordinates.size + 1) channels 0).reason ≠ .exhausted := by
  intro exhausted
  have stop := search_stop state (state.coordinates.size + 1) channels 0
  rw [exhausted] at stop
  have prefixMarked := search_prefix state (state.coordinates.size + 1) channels 0
  have bound := marked_bound state coherent (state.coordinates.size + 1) (by omega)
    (by intro index valid; simpa only [Nat.zero_add, stop.1] using prefixMarked index (by omega))
  omega

/-- The physical scan returns an unused source channel or covers all channels;
its completed reads are bounded by both actual counters. -/
theorem search_outcome (state : Dictionary ambient) (coherent : Coherent state)
    (channels : ℕ) (within : channels ≤ ambient) :
    ((search state (state.coordinates.size + 1) channels 0).reason = .unused ∧
      ∃ channel : Fin channels, state.slots[channel.val] = 0) ∨
    ((search state (state.coordinates.size + 1) channels 0).reason = .covered ∧
      channels ≤ state.coordinates.size ∧ ∀ channel : Fin channels, state.slots[channel.val] ≠ 0) := by
  let result := search state (state.coordinates.size + 1) channels 0
  have stop := search_stop state (state.coordinates.size + 1) channels 0
  have prefixMarked := search_prefix state (state.coordinates.size + 1) channels 0
  cases reason : result.reason with
  | exhausted => exact False.elim (search_not_exhausted state coherent channels within reason)
  | unused =>
      left
      refine ⟨rfl, ⟨⟨result.marked, ?_⟩, ?_⟩⟩
      · rw [show (search state (state.coordinates.size + 1) channels 0).reason = .unused from reason] at stop
        exact stop.2.1
      · have zero := stop
        rw [show (search state (state.coordinates.size + 1) channels 0).reason = .unused from reason] at zero
        simpa only [Nat.zero_add, slotAt, dite_eq_left (lt_of_lt_of_le zero.2.1 within)] using zero.1
  | covered =>
      rw [show (search state (state.coordinates.size + 1) channels 0).reason = .covered from reason] at stop
      have marked : ∀ index < channels, slotAt state index ≠ 0 := by
        intro index valid
        simpa only [Nat.zero_add, stop] using prefixMarked index (by omega)
      right
      refine ⟨rfl, marked_bound state coherent channels within marked, ?_⟩
      intro channel
      simpa only [slotAt, dite_eq_left (lt_of_lt_of_le channel.isLt within)] using marked channel.val channel.isLt


private theorem covered_execution (program : Program width 4) (heap : Array (Word width))
    (base budget pointer : ℕ) (stack output : List (Word width))
    (programFits : base + 13 < 2 ^ width) (block : BlockAt program base (code width base)) :
    Execution program (atState heap base 0 budget pointer 0 stack output)
      (atState heap (base + 11) 0 budget pointer 0 stack output)
      1 (5 + heap.size + stack.length + output.length) := by
  let first := atState heap base 0 budget pointer 0 stack output
  let final := atState heap (base + 11) 0 budget pointer 0 stack output
  have transition : programStep program first = some final := by
    rw [fetched program first base (.branchZero 0 (word width (base + 11))) rfl (by omega)
      (by simpa [code] using block 0 (by simp [code]))]
    change some (if (word width 0).val = 0 then { first.advance with pc := word width (base + 11) }
      else first.advance) = some final
    rw [show (word width 0).val = 0 from Nat.zero_mod _, ite_eq_left rfl,
      advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  convert Execution.cons transition (Execution.refl final) using 1 <;>
    simp only [first, final, atState_liveWords, Nat.max_self]

private theorem exhausted_execution (program : Program width 4) (heap : Array (Word width))
    (base left pointer : ℕ) (stack output : List (Word width))
    (leftFits : left + 1 < 2 ^ width) (programFits : base + 13 < 2 ^ width)
    (block : BlockAt program base (code width base)) :
    Execution program (atState heap base (left + 1) 0 pointer 0 stack output)
      (atState heap (base + 12) (left + 1) 0 pointer 0 stack output)
      2 (5 + heap.size + stack.length + output.length) := by
  let first := atState heap base (left + 1) 0 pointer 0 stack output
  let middle := atState heap (base + 1) (left + 1) 0 pointer 0 stack output
  let final := atState heap (base + 12) (left + 1) 0 pointer 0 stack output
  have t0 : programStep program first = some middle := by
    rw [fetched program first base (.branchZero 0 (word width (base + 11))) rfl (by omega)
      (by simpa [code] using block 0 (by simp [code]))]
    change some (if (word width (left + 1)).val = 0 then { first.advance with pc := word width (base + 11) }
      else first.advance) = some middle
    rw [show (word width (left + 1)).val = left + 1 from Nat.mod_eq_of_lt leftFits,
      ite_eq_right (by omega), advance_at _ _ _ _ _ _ _ _ (by omega)]
  have t1 : programStep program middle = some final := by
    rw [fetched program middle (base + 1) (.branchZero 1 (word width (base + 12))) rfl (by omega)
      (by simpa [code] using block 1 (by simp [code]))]
    change some (if (word width 0).val = 0 then { middle.advance with pc := word width (base + 12) }
      else middle.advance) = some final
    rw [show (word width 0).val = 0 from Nat.zero_mod _, ite_eq_left rfl,
      advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  convert Execution.cons t0 (Execution.cons t1 (Execution.refl final)) using 1 <;>
    simp only [first, middle, final, atState_liveWords, Nat.max_self]

/-- Complete physical countdown recursion follows the executable indexed
search. Every consulted natural slot is linked to its actual represented
heap word; the machine retains the heap and both caller frames. -/
theorem search_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (base : ℕ)
    (stack output : List (Word width)) (heapFits : heap.size < 2 ^ width)
    (countFits : state.coordinates.size + 1 < 2 ^ width)
    (programFits : base + 13 < 2 ^ width) (block : BlockAt program base (code width base))
    (budget channels offset : ℕ) (budgetFits : budget < 2 ^ width) (channelsFits : channels < 2 ^ width)
    (within : offset + channels ≤ ambient) :
    let result := search state budget channels offset
    Execution program (atState heap base channels budget (layout.tableBase + offset) 0 stack output)
      (atState heap (base + exitOffset result.reason) (channels - result.marked)
        (budget - result.marked) (layout.tableBase + offset + result.marked) 0 stack output)
      (11 * result.marked + exitTicks result.reason)
      (5 + heap.size + stack.length + output.length) := by
  induction budget generalizing channels offset with
  | zero =>
      cases channels with
      | zero =>
          simpa only [search, exitOffset, exitTicks, Nat.sub_zero, Nat.add_zero, Nat.zero_add,
            Nat.mul_zero] using (covered_execution program heap base 0 (layout.tableBase + offset)
              stack output programFits block)
      | succ channels =>
          simpa only [search, exitOffset, exitTicks, Nat.sub_zero, Nat.add_zero,
            Nat.zero_add, Nat.mul_zero] using (exhausted_execution program heap base channels
              (layout.tableBase + offset) stack output channelsFits programFits block)
  | succ budget ih =>
      cases channels with
      | zero =>
          simpa only [search, exitOffset, exitTicks, Nat.sub_zero, Nat.add_zero, Nat.zero_add,
            Nat.mul_zero] using (covered_execution program heap base (budget + 1) (layout.tableBase + offset)
              stack output programFits block)
      | succ channels =>
          have coordinateValid : offset < ambient := by omega
          let coordinate : Fin ambient := ⟨offset, coordinateValid⟩
          have cell : heap[layout.tableBase + offset]? = some (word width (slotAt state offset)) := by
            simpa only [coordinate, slotAt, dite_eq_left coordinateValid] using represented.slots coordinate
          have encodedFits : slotAt state offset < 2 ^ width := by
            have bounded := encoded_bound state represented.coherent coordinate
            simp only [coordinate, slotAt, dite_eq_left coordinateValid] at bounded ⊢
            omega
          have valid : layout.tableBase + offset < heap.size := layout.table_valid coordinate
          have pointerFits : layout.tableBase + offset + 1 < 2 ^ width := by
            have := layout.tableBound
            omega
          have read := read_execution program heap base channels budget (layout.tableBase + offset)
            (slotAt state offset) stack output channelsFits budgetFits (by omega) encodedFits valid cell
            programFits block
          by_cases unused : slotAt state offset = 0
          · rw [unused] at read
            simpa only [search, ite_eq_left unused, exitOffset, exitTicks, Nat.sub_zero, Nat.add_zero,
              Nat.mul_zero, Nat.zero_add, ite_true] using read
          · have read' : Execution program
                (atState heap base (channels + 1) (budget + 1) (layout.tableBase + offset) 0 stack output)
                (atState heap (base + 4) (channels + 1) (budget + 1) (layout.tableBase + offset)
                  (slotAt state offset) stack output) 4 (5 + heap.size + stack.length + output.length) := by
              simpa only [ite_eq_right unused] using read
            have updated := update_execution program heap base channels budget (layout.tableBase + offset)
              (slotAt state offset) stack output channelsFits budgetFits pointerFits programFits block
            have tail := ih channels (offset + 1) (by omega) (by omega) (by omega)
            have tail' : Execution program
                (atState heap base channels budget (layout.tableBase + offset + 1) 0 stack output)
                (atState heap (base + exitOffset (search state budget channels (offset + 1)).reason)
                  (channels - (search state budget channels (offset + 1)).marked)
                  (budget - (search state budget channels (offset + 1)).marked)
                  (layout.tableBase + offset + 1 + (search state budget channels (offset + 1)).marked)
                  0 stack output)
                (11 * (search state budget channels (offset + 1)).marked +
                  exitTicks (search state budget channels (offset + 1)).reason)
                (5 + heap.size + stack.length + output.length) := by
              simpa only [Nat.add_assoc] using tail
            have tailBounds := search_bounds state budget channels (offset + 1)
            have searchEq : search state (budget + 1) (channels + 1) offset =
                (search state budget channels (offset + 1)).bump := by
              rw [search, ite_eq_right unused]
            have joined := (read'.append updated).append tail'
            rw [searchEq]
            convert joined using 1 <;>
              simp only [Result.bump, Nat.succ_sub_succ_eq_sub,
                Nat.max_self, Nat.mul_add, Nat.mul_one, Nat.add_sub_add_right,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            all_goals first | omega | (congr 1 <;> omega)

/-- The executable physical scan has no exhausted branch for actual allocated
slots. Its cost is bounded by both the source channel count and count+one. -/
theorem bounded_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (base channels : ℕ)
    (stack output : List (Word width)) (within : channels ≤ ambient)
    (heapFits : heap.size < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + 13 < 2 ^ width) (block : BlockAt program base (code width base)) :
    let result := search state (state.coordinates.size + 1) channels 0
    ∃ ticks, Execution program
      (atState heap base channels (state.coordinates.size + 1) layout.tableBase 0 stack output)
      (atState heap (base + exitOffset result.reason) (channels - result.marked)
        (state.coordinates.size + 1 - result.marked) (layout.tableBase + result.marked) 0 stack output)
      ticks (5 + heap.size + stack.length + output.length) ∧
      ticks ≤ 11 * min channels (state.coordinates.size + 1) + 4 ∧
      result.reason ≠ .exhausted := by
  have countBound := count_le_ambient state represented.coherent
  have trace := search_execution program heap layout state represented base stack output heapFits
    (by omega) programFits block (state.coordinates.size + 1) channels 0 (by omega) (by omega) (by omega)
  refine ⟨11 * (search state (state.coordinates.size + 1) channels 0).marked +
    exitTicks (search state (state.coordinates.size + 1) channels 0).reason, ?_, ?_,
    search_not_exhausted state represented.coherent channels within⟩
  · simpa only [Nat.add_zero] using trace
  · have bounds := search_bounds state (state.coordinates.size + 1) channels 0
    have markedBound : (search state (state.coordinates.size + 1) channels 0).marked ≤
        min channels (state.coordinates.size + 1) := le_min bounds.2 bounds.1
    have exitBound : exitTicks (search state (state.coordinates.size + 1) channels 0).reason ≤ 4 := by
      cases (search state (state.coordinates.size + 1) channels 0).reason <;> decide
    omega


/-- Load the actual source channel count and form count-plus-one from the
physical allocator register, retaining its real table base in the pointer. -/
def entryCode (width : ℕ) : Code width :=
  [.constant 0 (word width 0), .load 0 0, .copy 3 2, .copy 2 1,
   .constant 1 (word width 1), .add 1 3 1, .constant 3 (word width 0)]

@[simp] theorem entryCode_length : (entryCode width).length = 7 := rfl

theorem entry_execution (program : Program width 4) (heap : Array (Word width))
    (base channels table count oldInput oldScratch : ℕ) (stack output : List (Word width))
    (valid : 0 < heap.size) (channelCell : heap[0]? = some (word width channels))
    (countFits : count + 1 < 2 ^ width) (programFits : base + 7 < 2 ^ width)
    (block : BlockAt program base (entryCode width)) :
    Execution program (atState heap base oldInput table count oldScratch stack output)
      (atState heap (base + 7) channels (count + 1) table 0 stack output)
      7 (5 + heap.size + stack.length + output.length) := by
  let s0 := atState heap base oldInput table count oldScratch stack output
  let s1 := atState heap (base + 1) 0 table count oldScratch stack output
  let s2 := atState heap (base + 2) channels table count oldScratch stack output
  let s3 := atState heap (base + 3) channels table count count stack output
  let s4 := atState heap (base + 4) channels table table count stack output
  let s5 := atState heap (base + 5) channels 1 table count stack output
  let s6 := atState heap (base + 6) channels (count + 1) table count stack output
  let s7 := atState heap (base + 7) channels (count + 1) table 0 stack output
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 base (.constant 0 (word width 0)) rfl (by omega)
      (by simpa [entryCode] using block 0 (by simp [entryCode]))]
    change some (s0.advance.put 0 (word width 0)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t1 : programStep program s1 = some s2 := by
    have actual : heap[0] = word width channels := by
      rw [Array.getElem?_eq_getElem valid] at channelCell
      exact Option.some.inj channelCell
    rw [fetched program s1 (base + 1) (.load 0 0) rfl (by omega)
      (by simpa [entryCode] using block 1 (by simp [entryCode]))]
    change (if bound : (word width 0).val < heap.size then
      some (s1.advance.put 0 heap[(word width 0).val]) else none) = some s2
    rw [show (word width 0).val = 0 from Nat.zero_mod _, dite_eq_left valid, actual,
      advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.copy 3 2) rfl (by omega)
      (by simpa [entryCode] using block 2 (by simp [entryCode]))]
    change some (s2.advance.put 3 (word width count)) = some s3
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.copy 2 1) rfl (by omega)
      (by simpa [entryCode] using block 3 (by simp [entryCode]))]
    change some (s3.advance.put 2 (word width table)) = some s4
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (base + 4) (.constant 1 (word width 1)) rfl (by omega)
      (by simpa [entryCode] using block 4 (by simp [entryCode]))]
    change some (s4.advance.put 1 (word width 1)) = some s5
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (base + 5) (.add 1 3 1) rfl (by omega)
      (by simpa [entryCode] using block 5 (by simp [entryCode]))]
    change some (s5.advance.put 1 (word width ((word width count).val + (word width 1).val))) = some s6
    rw [show (word width count).val = count from Nat.mod_eq_of_lt (by omega),
      show (word width 1).val = 1 from Nat.mod_eq_of_lt (by omega),
      advance_at _ _ _ _ _ _ _ _ (by omega), put1_at]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (base + 6) (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [entryCode] using block 6 (by simp [entryCode]))]
    change some (s6.advance.put 3 (word width 0)) = some s7
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have firstTrace := Execution.cons t0 (Execution.cons t1 (Execution.refl s2))
  have middleTrace := Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.refl s5)))
  have lastTrace := Execution.cons t5 (Execution.cons t6 (Execution.refl s7))
  convert (firstTrace.append middleTrace).append lastTrace using 1 <;>
    simp only [s0, s1, s2, s3, s4, s5, s6, s7, atState_liveWords, Nat.max_self]

def fullCode (width base : ℕ) : Code width := entryCode width ++ code width (base + 7)

@[simp] theorem fullCode_length : (fullCode width base).length = 18 := rfl

/-- The whole source-loaded support scan includes physical header/count
formation. Its dynamic bound uses the actual allocator count, not a supplied
precomputed minimum. Program size is eighteen fixed instructions. -/
theorem loaded_bounded_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (state : Dictionary ambient)
    (represented : Represented heap layout state) (base channels oldInput oldScratch : ℕ)
    (stack output : List (Word width)) (within : channels ≤ ambient)
    (channelCell : heap[0]? = some (word width channels)) (valid : 0 < heap.size)
    (heapFits : heap.size < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + 20 < 2 ^ width) (block : BlockAt program base (fullCode width base)) :
    let result := search state (state.coordinates.size + 1) channels 0
    ∃ ticks, Execution program
      (atState heap base oldInput layout.tableBase state.coordinates.size oldScratch stack output)
      (atState heap (base + 7 + exitOffset result.reason) (channels - result.marked)
        (state.coordinates.size + 1 - result.marked) (layout.tableBase + result.marked) 0 stack output)
      ticks (5 + heap.size + stack.length + output.length) ∧
      ticks ≤ 11 * min channels (state.coordinates.size + 1) + 11 ∧
      result.reason ≠ .exhausted := by
  have entryBlock := BlockAt.prefix program base _ _ block
  have scanBlock : BlockAt program (base + 7) (code width (base + 7)) := by
    simpa only [entryCode_length] using BlockAt.suffix program base _ _ block
  have countBound := count_le_ambient state represented.coherent
  have entry := entry_execution program heap base channels layout.tableBase state.coordinates.size
    oldInput oldScratch stack output valid channelCell (by omega) (by omega) entryBlock
  obtain ⟨ticks, scan, tickBound, notExhausted⟩ := bounded_execution program heap layout state represented
    (base + 7) channels stack output within heapFits ambientFits (by omega) scanBlock
  refine ⟨7 + ticks, ?_, by omega, notExhausted⟩
  simpa only [Nat.max_self] using entry.append scan

/-- An unused channel contributes nonemptiness only after an actual zero-row
model has been supplied. TRUE on unseen coordinates preserves that same model;
this statement does not infer detection from an unused slot alone. -/
theorem unused_preserves_existing_model (initial : Dictionary ambient) (coherent : Coherent initial)
    (rows : List (Clause (Fin ambient))) (channels : ℕ) (within : channels ≤ ambient)
    (values : ℕ → Bool) (model : Satisfies values (ofClauses (compileRows initial rows).2.1))
    (unused : (search (compileRows initial rows).1 ((compileRows initial rows).1.coordinates.size + 1)
      channels 0).reason = .unused) :
    Satisfies (ForestZeroModelLift.lift (compileRows initial rows).1 true values) (ofClauses rows) ∧
      ∃ channel : Fin channels,
        ForestZeroModelLift.lift (compileRows initial rows).1 true values
          ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ = true := by
  have finalCoherent := (rows_dictionary initial coherent rows).1
  have outcome := search_outcome (compileRows initial rows).1 finalCoherent channels within
  refine ⟨(ForestZeroModelLift.rows_lift_model initial coherent rows true values).mp model, ?_⟩
  rcases outcome with ⟨_, channel, zero⟩ | ⟨covered, _, _⟩
  · exact ⟨channel, ForestZeroModelLift.lift_unseen _ true values _ zero⟩
  · have impossible : Reason.unused = .covered := unused.symm.trans covered
    cases impossible


end Controller.Cost.ForestZeroNonempty
