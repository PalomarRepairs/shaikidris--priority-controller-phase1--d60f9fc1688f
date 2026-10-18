module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.Encoding
public import Controller.Complexity.Reductions
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-! Uniform binary addition and XOR routines. Operand bits reside on two private
stacks in least-significant-first order. The shared stack receives the result
in reverse order. Addition carries use finite control, and overflow is discarded. -/
namespace Controller.Complexity.WordArithmetic
open StackMachine
open scoped BigOperators

abbrev Label := Option (Fin 3 × Bool × Bool)

def entry (carry : Bool) : Label := some (0, false, carry)
def readRight (left carry : Bool) : Label := some (1, left, carry)
def writeBit (bit carry : Bool) : Label := some (2, bit, carry)

def sumBit (left right carry : Bool) : Bool := (left ^^ right) ^^ carry
def carryBit (left right carry : Bool) : Bool := (left && right) || (carry && (left || right))

def program : Program Bool Label where
  main := entry false
  code label := match label with
    | none => .halt
    | some (phase, bit, carry) => match phase.val with
      | 0 => .pop (some false) none (readRight false carry) (readRight true carry)
      | 1 => .pop (some true) none
          (writeBit (sumBit bit false carry) (carryBit bit false carry))
          (writeBit (sumBit bit true carry) (carryBit bit true carry))
      | _ => .push none bit (entry carry)

def state (label : Option Label) (left right output : List Bool) : State Bool Label :=
  ⟨label, fun stack => match stack with | none => output | some false => left | some true => right⟩

theorem live_state (label) (left right output : List Bool) :
    live (state label left right output) = left.length + right.length + output.length := by
  simp [live, Fintype.sum_option, state, Nat.add_comm]

def addBits (carry : Bool) : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | left :: restLeft, right :: restRight =>
    sumBit left right carry :: addBits (carryBit left right carry) restLeft restRight

theorem pop_left (carry leftBit : Bool) (left right output : List Bool) :
    step program (state (some (entry carry)) (leftBit :: left) right output) =
      some (state (some (readRight leftBit carry)) left right output) := by
  cases carry <;> cases leftBit <;>
    simp [step, program, entry, readRight, instructionStep, state]
  all_goals funext stack; cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl

theorem pop_right (carry leftBit rightBit : Bool) (left right output : List Bool) :
    step program (state (some (readRight leftBit carry)) left (rightBit :: right) output) =
      some (state (some (writeBit (sumBit leftBit rightBit carry) (carryBit leftBit rightBit carry)))
        left right output) := by
  cases carry <;> cases leftBit <;> cases rightBit <;>
    simp [step, program, readRight, writeBit, instructionStep, state, sumBit, carryBit]
  all_goals funext stack; cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl

theorem push_sum (bit carry : Bool) (left right output : List Bool) :
    step program (state (some (writeBit bit carry)) left right output) =
      some (state (some (entry carry)) left right (bit :: output)) := by
  cases bit <;> cases carry <;>
    simp [step, program, writeBit, entry, instructionStep, state]
  all_goals funext stack; cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl

theorem pop_empty (carry : Bool) (output : List Bool) :
    step program (state (some (entry carry)) [] [] output) = some (state (some none) [] [] output) := by
  cases carry <;> simp [step, program, entry, instructionStep, state]

theorem halt (output : List Bool) :
    step program (state (some none) [] [] output) = some (terminal output) := by
  simp only [step, program, state, instructionStep, terminal, Option.map_some]
  congr 2
  funext stack
  cases stack with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem execution (carry : Bool) (left right output : List Bool) (sameLength : left.length = right.length) :
    Execution program (state (some (entry carry)) left right output)
      (terminal ((addBits carry left right).reverse ++ output))
      (3*left.length+2) (left.length+right.length+output.length) := by
  induction left generalizing right output carry with
  | nil =>
    have rightEmpty : right = [] := List.eq_nil_iff_length_eq_zero.mpr sameLength.symm
    subst right
    have done : Execution program (terminal (K := Bool) (Q := Label) output) (terminal output) 0 output.length := by
      simpa only [live_terminal] using Execution.refl (program := program) (terminal output)
    have tail := Execution.cons (halt output) done
    have trace := Execution.cons (pop_empty carry output) tail
    simpa [addBits, live_state] using trace
  | cons leftBit left ih =>
    cases right with
    | nil => simp at sameLength
    | cons rightBit right =>
      have equalTails : left.length = right.length := by simpa using sameLength
      have tail := ih (carryBit leftBit rightBit carry) right (sumBit leftBit rightBit carry :: output) equalTails
      have one := Execution.cons (push_sum (sumBit leftBit rightBit carry) (carryBit leftBit rightBit carry) left right output) tail
      have two := Execution.cons (pop_right carry leftBit rightBit left right output) one
      have three := Execution.cons (pop_left carry leftBit left (rightBit :: right) output) two
      have count : ((3*left.length+2)+1)+1+1 = 3*(leftBit :: left).length+2 := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      rw [count] at three
      simpa [addBits, List.reverse_cons, List.append_assoc, live_state, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.max_eq_left] using three

theorem full_adder (left right : Nat) (carry : Bool) :
    decide ((left+right+(if carry then 1 else 0))%2=1) =
      sumBit (decide (left%2=1)) (decide (right%2=1)) carry ∧
    (left+right+(if carry then 1 else 0))/2 = left/2+right/2+
      (if carryBit (decide (left%2=1)) (decide (right%2=1)) carry then 1 else 0) := by
  have leftRemainder : left%2=0 ∨ left%2=1 := by omega
  have rightRemainder : right%2=0 ∨ right%2=1 := by omega
  rcases leftRemainder with hl | hl <;> rcases rightRemainder with hr | hr <;> cases carry <;>
    constructor <;> simp [hl, hr, sumBit, carryBit] <;> omega

theorem addBits_bits (carry : Bool) (width left right : Nat) :
    addBits carry (Encoding.bits width left) (Encoding.bits width right) =
      Encoding.bits width (left+right+(if carry then 1 else 0)) := by
  induction width generalizing left right carry with
  | zero => rfl
  | succ width ih =>
    have split := full_adder left right carry
    simp only [Encoding.bits, addBits]
    rw [split.1, split.2]
    exact congrArg (sumBit (decide (left%2=1)) (decide (right%2=1)) carry :: ·)
      (ih (carryBit (decide (left%2=1)) (decide (right%2=1)) carry) (left/2) (right/2))

theorem value_bits_mod (width value : Nat) :
    Encoding.value (Encoding.bits width value) = value % 2^width := by
  induction width generalizing value with
  | zero => simp only [Encoding.bits, Encoding.value, Nat.pow_zero, Nat.mod_one]
  | succ width ih =>
    have parity : (if decide (value%2=1) then 1 else 0) = value%2 := by
      split <;> rename_i h <;> simp_all
    have split : Encoding.value (Encoding.bits (width+1) value) +
        2^(width+1)*((value/2)/2^width) = value := by
      simp only [Encoding.bits, Encoding.value, ih, parity]
      calc
        _ = 2*((value/2)%2^width + 2^width*((value/2)/2^width)) + value%2 := by
          simp only [Nat.pow_succ, Nat.mul_add, Nat.mul_assoc]
          ac_rfl
        _ = value := by rw [Nat.mod_add_div]; omega
    have bound : Encoding.value (Encoding.bits (width+1) value) < 2^(width+1) := by
      simpa only [Encoding.bits_length] using (Encoding.value_lt (Encoding.bits (width+1) value))
    calc
      Encoding.value (Encoding.bits (width+1) value) =
          Encoding.value (Encoding.bits (width+1) value) % 2^(width+1) :=
        (Nat.mod_eq_of_lt bound).symm
      _ = (Encoding.value (Encoding.bits (width+1) value) +
          2^(width+1)*((value/2)/2^width)) % 2^(width+1) := by simp
      _ = value % 2^(width+1) := congrArg (· % 2^(width+1)) split

theorem decode_sum (width left right : Nat) :
    Encoding.decodeWord width (Encoding.bits width (left+right)) =
      some (Controller.Cost.word width (left+right)) := by
  simp [Encoding.decodeWord, Encoding.bits_length, value_bits_mod, Controller.Cost.word]

/-- A fixed finite program adds arbitrary-width words, discarding overflow.
The operand stacks are consumed and the shared result is most-significant-first. -/
theorem encoded_execution (width left right : Nat) (output : List Bool) :
    Execution program
      (state (some (entry false)) (Encoding.bits width left) (Encoding.bits width right) output)
      (terminal ((Encoding.bits width (left+right)).reverse ++ output))
      (3*width+2) (2*width+output.length) := by
  have trace := execution false (Encoding.bits width left) (Encoding.bits width right) output (by simp)
  simpa only [addBits_bits, Bool.false_eq_true, ite_false, Nat.add_zero, Encoding.bits_length,
    two_mul] using trace

theorem program_resident :
    (∑ label, statementSize (tmStatement (program.code label))) ≤ 117 := by
  simpa [Label] using finiteTM_resident program

end Controller.Complexity.WordArithmetic

/-! The XOR routine shares the addition operand convention. -/
namespace Controller.Complexity.WordXor
open StackMachine
open scoped BigOperators

abbrev Label := Option (Fin 3 × Bool)
def entry : Label := some (0, false)
def readRight (left : Bool) : Label := some (1, left)
def writeBit (bit : Bool) : Label := some (2, bit)

def program : Program Bool Label where
  main := entry
  code label := match label with
    | none => .halt
    | some (phase, bit) => match phase.val with
      | 0 => .pop (some false) none (readRight false) (readRight true)
      | 1 => .pop (some true) none (writeBit (bit ^^ false)) (writeBit (bit ^^ true))
      | _ => .push none bit entry

def state (label : Option Label) (left right output : List Bool) : State Bool Label :=
  ⟨label, fun stack => match stack with | none => output | some false => left | some true => right⟩

theorem live_state (label) (left right output : List Bool) :
    live (state label left right output) = left.length + right.length + output.length := by
  simp [live, Fintype.sum_option, state, Nat.add_comm]

def xorBits : List Bool → List Bool → List Bool
  | [], _ => []
  | _, [] => []
  | left :: restLeft, right :: restRight => (left ^^ right) :: xorBits restLeft restRight

theorem pop_left (leftBit : Bool) (left right output : List Bool) :
    step program (state (some entry) (leftBit :: left) right output) =
      some (state (some (readRight leftBit)) left right output) := by
  cases leftBit <;> simp [step, program, entry, readRight, instructionStep, state]
  all_goals funext stack; cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl

theorem pop_right (leftBit rightBit : Bool) (left right output : List Bool) :
    step program (state (some (readRight leftBit)) left (rightBit :: right) output) =
      some (state (some (writeBit (leftBit ^^ rightBit))) left right output) := by
  cases leftBit <;> cases rightBit <;>
    simp [step, program, readRight, writeBit, instructionStep, state]
  all_goals funext stack; cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl

theorem push_result (bit : Bool) (left right output : List Bool) :
    step program (state (some (writeBit bit)) left right output) =
      some (state (some entry) left right (bit :: output)) := by
  cases bit <;> simp [step, program, writeBit, entry, instructionStep, state]
  all_goals funext stack; cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl

theorem pop_empty (output : List Bool) :
    step program (state (some entry) [] [] output) = some (state (some none) [] [] output) := by
  simp [step, program, entry, instructionStep, state]

theorem halt (output : List Bool) :
    step program (state (some none) [] [] output) = some (terminal output) := by
  simp only [step, program, state, instructionStep, terminal, Option.map_some]
  congr 2
  funext stack
  cases stack with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem execution (left right output : List Bool) (sameLength : left.length = right.length) :
    Execution program (state (some entry) left right output)
      (terminal ((xorBits left right).reverse ++ output))
      (3*left.length+2) (left.length+right.length+output.length) := by
  induction left generalizing right output with
  | nil =>
    have rightEmpty : right = [] := List.eq_nil_iff_length_eq_zero.mpr sameLength.symm
    subst right
    have done : Execution program (terminal (K := Bool) (Q := Label) output) (terminal output) 0 output.length := by
      simpa only [live_terminal] using Execution.refl (program := program) (terminal output)
    have trace := Execution.cons (pop_empty output) (Execution.cons (halt output) done)
    simpa [xorBits, live_state] using trace
  | cons leftBit left ih =>
    cases right with
    | nil => simp at sameLength
    | cons rightBit right =>
      have equalTails : left.length = right.length := by simpa using sameLength
      have tail := ih right ((leftBit ^^ rightBit) :: output) equalTails
      have one := Execution.cons (push_result (leftBit ^^ rightBit) left right output) tail
      have two := Execution.cons (pop_right leftBit rightBit left right output) one
      have three := Execution.cons (pop_left leftBit left (rightBit :: right) output) two
      have count : ((3*left.length+2)+1)+1+1 = 3*(leftBit :: left).length+2 := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      rw [count] at three
      simpa [xorBits, List.reverse_cons, List.append_assoc, live_state, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.max_eq_left] using three

theorem xor_low_bit (left right : Nat) :
    decide ((left ^^^ right)%2=1) = (decide (left%2=1) ^^ decide (right%2=1)) := by
  simpa only [Nat.testBit_zero] using Nat.testBit_xor left right 0

theorem xorBits_bits (width left right : Nat) :
    xorBits (Encoding.bits width left) (Encoding.bits width right) = Encoding.bits width (left ^^^ right) := by
  induction width generalizing left right with
  | zero => rfl
  | succ width ih =>
    simp only [Encoding.bits, xorBits, Nat.xor_div_two, xor_low_bit, ih]

theorem decode_xor (width left right : Nat) :
    Encoding.decodeWord width (Encoding.bits width (left ^^^ right)) =
      some (Controller.Cost.word width (Nat.xor left right)) := by
  simp [Encoding.decodeWord, Encoding.bits_length, WordArithmetic.value_bits_mod, Controller.Cost.word]

theorem encoded_execution (width left right : Nat) (output : List Bool) :
    Execution program
      (state (some entry) (Encoding.bits width left) (Encoding.bits width right) output)
      (terminal ((Encoding.bits width (left ^^^ right)).reverse ++ output))
      (3*width+2) (2*width+output.length) := by
  have trace := execution (Encoding.bits width left) (Encoding.bits width right) output (by simp)
  simpa only [xorBits_bits, Encoding.bits_length, two_mul] using trace

theorem program_resident :
    (∑ label, statementSize (tmStatement (program.code label))) ≤ 63 := by
  simpa [Label] using finiteTM_resident program

end Controller.Complexity.WordXor
