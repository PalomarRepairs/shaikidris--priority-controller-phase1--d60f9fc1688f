module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationSlots
public import Controller.Cost.ForestZeroAdmissibleCaller

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! One immutable unit-slot block. Heap mask words select one of three resident
literal emitters. All branches return to a common address; source coordinates,
dictionary storage, caller stack and output use the existing literal contract. -/
namespace Controller.Cost.EnumerationSlotCode
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile

def maskCode (width address absent : Nat) : Code width :=
  [.constant 0 (word width address), .load 0 0, .branchZero 0 (word width absent)]

@[simp] theorem maskCode_length : (maskCode width address absent).length = 3 := rfl

private theorem fetched (program : Program width 4) (state : State width 4)
    (cursor : Nat) (instruction : Instruction width 4)
    (position : state.pc = word width cursor) (room : cursor < 2 ^ width)
    (present : program[cursor]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, show (word width cursor).val = cursor from Nat.mod_eq_of_lt room, present]
  rfl

private theorem advance_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 : Nat)
    (stack output : List (Word width)) (room : cursor < 2 ^ width) :
    (atState heap cursor x0 x1 x2 x3 stack output).advance =
      atState heap (cursor + 1) x0 x1 x2 x3 stack output := by
  simp [atState, State.advance, show (word width cursor).val = cursor from Nat.mod_eq_of_lt room]

private theorem put0_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : Nat)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 0 (word width value) =
      atState heap cursor value x1 x2 x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

/-- Three fetched instructions read a mask without changing storage or the
allocator registers. Both branch outcomes are covered by the same trace. -/
theorem mask_execution (program : Program width 4) (heap : Array (Word width))
    (base address absent input table count scratch : Nat) (value : Bool)
    (stack output : List (Word width)) (widthPositive : 0 < width)
    (addressFits : address < 2 ^ width) (valid : address < heap.size)
    (stored : heap[address]? = some (boolWord width value))
    (room : base + 3 < 2 ^ width) (block : BlockAt program base (maskCode width address absent)) :
    Execution program (atState heap base input table count scratch stack output)
      (atState heap (if value then base + 3 else absent) (if value then 1 else 0)
        table count scratch stack output) 3 (5 + heap.size + stack.length + output.length) := by
  let s0 := atState heap base input table count scratch stack output
  let s1 := atState heap (base + 1) address table count scratch stack output
  let s2 := atState heap (base + 2) (if value then 1 else 0) table count scratch stack output
  let s3 := atState heap (if value then base + 3 else absent) (if value then 1 else 0)
    table count scratch stack output
  have addressWord : (word width address).val = address := Nat.mod_eq_of_lt addressFits
  have oneFits : 1 < 2 ^ width := by
    have power := Nat.pow_lt_pow_right (by decide : 1 < 2) widthPositive
    simpa using power
  have maskWord : boolWord width value = word width (if value then 1 else 0) := by
    cases value <;> rfl
  have actual : heap[address] = word width (if value then 1 else 0) := by
    rw [Array.getElem?_eq_getElem valid, maskWord] at stored
    exact Option.some.inj stored
  have first : programStep program s0 = some s1 := by
    rw [fetched program s0 base _ rfl (by omega)
      (by simpa [maskCode] using block 0 (by simp [maskCode]))]
    change some (s0.advance.put 0 (word width address)) = some s1
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have second : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) _ rfl (by omega)
      (by simpa [maskCode] using block 1 (by simp [maskCode]))]
    simp only [step, s1, atState, Bool.false_eq_true, ite_false, ite_true, addressWord,
      valid, actual]
    change some ((atState heap (base + 1) address table count scratch stack output).advance.put 0
      (word width (if value then 1 else 0))) = some s2
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have third : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) _ rfl (by omega)
      (by simpa [maskCode] using block 2 (by simp [maskCode]))]
    cases value <;>
      simp [step, s2, s3, atState, State.advance, word, Nat.mod_eq_of_lt oneFits,
        Nat.add_assoc, Nat.mod_eq_of_lt (by omega : base + 2 < 2 ^ width)]
  simpa only [s0, s1, s2, s3, atState_liveWords, Nat.max_self, Nat.reduceAdd] using
    Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl s3)))

def code (width base trueMask falseMask : Nat)
    (positive negative inactive : Reference ambient) : Code width :=
  maskCode width trueMask (base + 30) ++
  (literalCode width (base + 3) positive ++ (ForestZeroAdmissibleCaller.jumpCode width (base + 90) ++
  (maskCode width falseMask (base + 60) ++
  (literalCode width (base + 33) negative ++ (ForestZeroAdmissibleCaller.jumpCode width (base + 90) ++
  (literalCode width (base + 60) inactive ++ ForestZeroAdmissibleCaller.jumpCode width (base + 90)))))))

@[simp] theorem code_length (positive negative inactive : Reference ambient)
    (positiveChannel : positive.activity = false) (negativeChannel : negative.activity = false)
    (inactiveRoot : inactive.activity = true) :
    (code width base trueMask falseMask positive negative inactive).length = 90 := by
  simp [code, literalCode_length, readCode_length, positiveChannel, negativeChannel, inactiveRoot,
    ForestZeroAdmissibleCaller.jumpCode]

def selected (positive negative inactive : Reference ambient) (trueFlag falseFlag : Bool) : Reference ambient :=
  if trueFlag then positive else if falseFlag then negative else inactive

theorem blocks (program : Program width 4) (positive negative inactive : Reference ambient)
    (positiveChannel : positive.activity = false) (negativeChannel : negative.activity = false)
    (inactiveRoot : inactive.activity = true)
    (whole : BlockAt program base (code width base trueMask falseMask positive negative inactive)) :
    BlockAt program base (maskCode width trueMask (base + 30)) ∧
    BlockAt program (base + 3) (literalCode width (base + 3) positive) ∧
    BlockAt program (base + 28) (ForestZeroAdmissibleCaller.jumpCode width (base + 90)) ∧
    BlockAt program (base + 30) (maskCode width falseMask (base + 60)) ∧
    BlockAt program (base + 33) (literalCode width (base + 33) negative) ∧
    BlockAt program (base + 58) (ForestZeroAdmissibleCaller.jumpCode width (base + 90)) ∧
    BlockAt program (base + 60) (literalCode width (base + 60) inactive) ∧
    BlockAt program (base + 88) (ForestZeroAdmissibleCaller.jumpCode width (base + 90)) := by
  unfold code at whole
  have first := BlockAt.prefix program base _ _ whole
  have rest1 := BlockAt.suffix program base _ _ whole
  simp only [maskCode_length] at rest1
  have second := BlockAt.prefix program (base + 3) _ _ rest1
  have rest2 := BlockAt.suffix program (base + 3) _ _ rest1
  simp only [literalCode_length, readCode_length, positiveChannel, Nat.add_assoc] at rest2
  have third := BlockAt.prefix program (base + 28) _ _ rest2
  have rest3 := BlockAt.suffix program (base + 28) _ _ rest2
  simp only [ForestZeroAdmissibleCaller.jumpCode, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.add_assoc] at rest3
  have fourth := BlockAt.prefix program (base + 30) _ _ rest3
  have rest4 := BlockAt.suffix program (base + 30) _ _ rest3
  simp only [maskCode_length, Nat.add_assoc, Nat.reduceAdd] at rest4
  have fifth := BlockAt.prefix program (base + 33) _ _ rest4
  have rest5 := BlockAt.suffix program (base + 33) _ _ rest4
  simp only [literalCode_length, readCode_length, negativeChannel, Nat.add_assoc] at rest5
  have sixth := BlockAt.prefix program (base + 58) _ _ rest5
  have rest6 := BlockAt.suffix program (base + 58) _ _ rest5
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.add_assoc] at rest6
  have seventh := BlockAt.prefix program (base + 60) _ _ rest6
  have last := BlockAt.suffix program (base + 60) _ _ rest6
  simp only [literalCode_length, readCode_length, inactiveRoot, ite_true,
    Nat.reduceAdd, Nat.add_assoc] at last
  exact ⟨first, second, third, fourth, fifth, sixth, seventh, last⟩

end Controller.Cost.EnumerationSlotCode
