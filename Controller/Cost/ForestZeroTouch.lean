module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroCompile
public import Controller.Cost.ForestMarkerMachine
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! A fixed first-touch program uses a shared slot table and a reserved inverse
coordinate region. Their initialization is charged once by the caller. The
inverse-region base is a real stack word retained at every call boundary.
Fresh coordinates perform two indexed stores; repeated coordinates perform no
store. The code never allocates an inverse array per root or constructs routes.
-/
namespace Controller.Cost.ForestZeroTouch
open Controller.Cost.GateProgram
variable {width : ℕ}

/-- Existing entries are decoded by modular addition of minus one. -/
def code (width base : ℕ) : Code width :=
  [.push 0, .add 3 0 1, .load 0 3, .branchZero 0 (word width (base + 9)),
   .constant 3 (word width (2 ^ width - 1)), .add 0 0 3, .pop 3,
   .constant 3 (word width 0), .branchZero 3 (word width (base + 20)),
   .constant 0 (word width 1), .add 0 2 0, .store 3 0,
   .pop 0, .pop 3, .push 3, .add 3 3 2, .store 3 0, .copy 0 2,
   .constant 3 (word width 1), .add 2 2 3]

@[simp] theorem code_length : (code width base).length = 20 := rfl

def atState (heap : Array (Word width)) (cursor x0 x1 x2 x3 : ℕ)
    (stack output : List (Word width)) : State width 4 where
  reg := fun register => if register = 0 then word width x0 else
    if register = 1 then word width x1 else if register = 2 then word width x2 else word width x3
  heap := heap
  stack := stack
  output := output
  pc := word width cursor
  halted := false

@[simp] theorem atState_liveWords (heap : Array (Word width)) (cursor x0 x1 x2 x3 : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).liveWords =
      5 + heap.size + stack.length + output.length := by
  simp [atState, State.liveWords]
  omega

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

private theorem put2_at (heap : Array (Word width)) (cursor x0 x1 x2 x3 value : ℕ)
    (stack output : List (Word width)) :
    (atState heap cursor x0 x1 x2 x3 stack output).put 2 (word width value) =
      atState heap cursor x0 x1 value x3 stack output := by
  unfold atState State.put
  congr 1
  funext register
  fin_cases register <;> rfl

/-- The first four actual fetched instructions push the original coordinate,
compute its slot address, load its encoded ID, and select the real branch. -/
theorem prefix_execution (program : Program width 4) (heap : Array (Word width))
    (base coordinate tableBase count scratch encoded : ℕ)
    (stack output : List (Word width))
    (addressFits : coordinate + tableBase < 2 ^ width)
    (addressValid : coordinate + tableBase < heap.size)
    (encodedFits : encoded < 2 ^ width)
    (stored : heap[coordinate + tableBase]'addressValid = word width encoded)
    (programFits : base + 20 < 2 ^ width)
    (block : BlockAt program base (code width base)) :
    Execution program (atState heap base coordinate tableBase count scratch stack output)
      (atState heap (if encoded = 0 then base + 9 else base + 4)
        encoded tableBase count (coordinate + tableBase)
        (word width coordinate :: stack) output)
      4 (6 + heap.size + stack.length + output.length) := by
  let initial := atState heap base coordinate tableBase count scratch stack output
  let one := atState heap (base + 1) coordinate tableBase count scratch
    (word width coordinate :: stack) output
  let two := atState heap (base + 2) coordinate tableBase count (coordinate + tableBase)
    (word width coordinate :: stack) output
  let three := atState heap (base + 3) encoded tableBase count (coordinate + tableBase)
    (word width coordinate :: stack) output
  let final := atState heap (if encoded = 0 then base + 9 else base + 4)
    encoded tableBase count (coordinate + tableBase) (word width coordinate :: stack) output
  have coordinateWord : (word width coordinate).val = coordinate := Nat.mod_eq_of_lt (by omega)
  have tableWord : (word width tableBase).val = tableBase := Nat.mod_eq_of_lt (by omega)
  have addressWord : (word width (coordinate + tableBase)).val = coordinate + tableBase :=
    Nat.mod_eq_of_lt addressFits
  have encodedWord : (word width encoded).val = encoded := Nat.mod_eq_of_lt encodedFits
  have pc0 : (word width base).val = base := Nat.mod_eq_of_lt (by omega)
  have pc1 : (word width (base + 1)).val = base + 1 := Nat.mod_eq_of_lt (by omega)
  have pc2 : (word width (base + 2)).val = base + 2 := Nat.mod_eq_of_lt (by omega)
  have pc3 : (word width (base + 3)).val = base + 3 := Nat.mod_eq_of_lt (by omega)
  have step0 : programStep program initial = some one := by
    rw [fetched program initial base (.push 0) rfl (by omega)
      (by simpa [code] using block 0 (by simp [code]))]
    simp [step, initial, one, atState, State.advance, pc0]
  have step1 : programStep program one = some two := by
    rw [fetched program one (base + 1) (.add 3 0 1) rfl (by omega)
      (by simpa [code] using block 1 (by simp [code]))]
    simp [step, one, two, atState, State.advance, State.put, pc1, coordinateWord, tableWord]
    congr 1
    funext register
    fin_cases register <;> rfl
  have step2 : programStep program two = some three := by
    rw [fetched program two (base + 2) (.load 0 3) rfl (by omega)
      (by simpa [code] using block 2 (by simp [code]))]
    simp [step, two, three, atState, State.advance, State.put, pc2, addressWord,
      addressValid, stored]
    funext register
    fin_cases register <;> rfl
  have step3 : programStep program three = some final := by
    rw [fetched program three (base + 3) (.branchZero 0 (word width (base + 9))) rfl (by omega)
      (by simpa [code] using block 3 (by simp [code]))]
    by_cases zero : encoded = 0 <;>
      simp [step, three, final, atState, State.advance, pc3, encodedWord, zero, word, Nat.mod_eq_of_lt encodedFits]
  have left := Execution.cons step0 (Execution.cons step1 (Execution.refl two))
  have right := Execution.cons step2 (Execution.cons step3 (Execution.refl final))
  have joined := left.append right
  have initialWords : initial.liveWords = 5 + heap.size + stack.length + output.length := by
    exact atState_liveWords _ _ _ _ _ _ _ _
  have oneWords : one.liveWords = 6 + heap.size + stack.length + output.length := by
    simp [one]; omega
  have twoWords : two.liveWords = 6 + heap.size + stack.length + output.length := by
    simp [two]; omega
  have threeWords : three.liveWords = 6 + heap.size + stack.length + output.length := by
    simp [three]; omega
  have finalWords : final.liveWords = 6 + heap.size + stack.length + output.length := by
    simp [final]; omega
  simpa only [initialWords, oneWords, twoWords, threeWords, finalWords,
    Nat.max_self, Nat.max_eq_right (show 5 + heap.size + stack.length + output.length ≤
      6 + heap.size + stack.length + output.length by omega), Nat.zero_add] using joined

/-- A repeated coordinate decodes its positive stored ID without writing the
slot table or the inverse region. The saved coordinate is popped once. -/
theorem existing_execution (program : Program width 4) (heap : Array (Word width))
    (base encoded tableBase count address coordinate : ℕ)
    (stack output : List (Word width)) (positive : 0 < encoded)
    (encodedFits : encoded < 2 ^ width) (programFits : base + 20 < 2 ^ width)
    (block : BlockAt program base (code width base)) :
    Execution program
      (atState heap (base + 4) encoded tableBase count address (word width coordinate :: stack) output)
      (atState heap (base + 20) (encoded - 1) tableBase count 0 stack output)
      5 (6 + heap.size + stack.length + output.length) := by
  let initial := atState heap (base + 4) encoded tableBase count address
    (word width coordinate :: stack) output
  let one := atState heap (base + 5) encoded tableBase count (2 ^ width - 1)
    (word width coordinate :: stack) output
  let two := atState heap (base + 6) (encoded - 1) tableBase count (2 ^ width - 1)
    (word width coordinate :: stack) output
  let three := atState heap (base + 7) (encoded - 1) tableBase count coordinate stack output
  let four := atState heap (base + 8) (encoded - 1) tableBase count 0 stack output
  let final := atState heap (base + 20) (encoded - 1) tableBase count 0 stack output
  have maximumFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have decoded : word width (encoded + (2 ^ width - 1)) = word width (encoded - 1) := by
    apply Fin.ext
    have same : encoded + (2 ^ width - 1) = (encoded - 1) + 2 ^ width := by omega
    simp only [word, same, Nat.add_mod_right]
  have step4 : programStep program initial = some one := by
    rw [fetched program initial (base + 4) (.constant 3 (word width (2 ^ width - 1))) rfl
      (by omega) (by simpa [code] using block 4 (by simp [code]))]
    change some (initial.advance.put 3 (word width (2 ^ width - 1))) = some one
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have step5 : programStep program one = some two := by
    rw [fetched program one (base + 5) (.add 0 0 3) rfl (by omega)
      (by simpa [code] using block 5 (by simp [code]))]
    change some (one.advance.put 0
      (word width ((word width encoded).val + (word width (2 ^ width - 1)).val))) = some two
    rw [show (word width encoded).val = encoded from Nat.mod_eq_of_lt encodedFits,
      show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from Nat.mod_eq_of_lt maximumFits,
      decoded, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have step6 : programStep program two = some three := by
    rw [fetched program two (base + 6) (.pop 3) rfl (by omega)
      (by simpa [code] using block 6 (by simp [code]))]
    change some { two.advance.put 3 (word width coordinate) with stack := stack } = some three
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
    rfl
  have step7 : programStep program three = some four := by
    rw [fetched program three (base + 7) (.constant 3 (word width 0)) rfl (by omega)
      (by simpa [code] using block 7 (by simp [code]))]
    change some (three.advance.put 3 (word width 0)) = some four
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have step8 : programStep program four = some final := by
    rw [fetched program four (base + 8) (.branchZero 3 (word width (base + 20))) rfl (by omega)
      (by simpa [code] using block 8 (by simp [code]))]
    change some (if (word width 0).val = 0 then
      { four.advance with pc := word width (base + 20) } else four.advance) = some final
    simp only [word, Nat.zero_mod, ite_true]
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  have left := Execution.cons step4 (Execution.cons step5 (Execution.refl two))
  have right := Execution.cons step6 (Execution.cons step7 (Execution.cons step8 (Execution.refl final)))
  have joined := left.append right
  have words0 : initial.liveWords = 6 + heap.size + stack.length + output.length := by simp [initial]; omega
  have words1 : one.liveWords = 6 + heap.size + stack.length + output.length := by simp [one]; omega
  have words2 : two.liveWords = 6 + heap.size + stack.length + output.length := by simp [two]; omega
  have words3 : three.liveWords = 5 + heap.size + stack.length + output.length := by exact atState_liveWords _ _ _ _ _ _ _ _
  have words4 : four.liveWords = 5 + heap.size + stack.length + output.length := by exact atState_liveWords _ _ _ _ _ _ _ _
  have words5 : final.liveWords = 5 + heap.size + stack.length + output.length := by exact atState_liveWords _ _ _ _ _ _ _ _
  simpa only [words0, words1, words2, words3, words4, words5, Nat.max_self,
    Nat.max_eq_left (show 5 + heap.size + stack.length + output.length ≤
      6 + heap.size + stack.length + output.length by omega), Nat.zero_add] using joined

/-- A first touch updates the indexed slot and the reserved inverse-coordinate
cell, restores its real base stack word, and increments the local count once.
No source or inverse array is reallocated by this per-coordinate path. -/
theorem fresh_execution (program : Program width 4) (heap : Array (Word width))
    (base coordinate tableBase count address inverseBase : ℕ)
    (stack output : List (Word width))
    (addressFits : address < 2 ^ width) (addressValid : address < heap.size)
    (countFits : count + 1 < 2 ^ width)
    (inverseFits : inverseBase + count < 2 ^ width)
    (inverseValid : inverseBase + count < heap.size)
    (programFits : base + 20 < 2 ^ width)
    (block : BlockAt program base (code width base)) :
    Execution program
      (atState heap (base + 9) 0 tableBase count address
        (word width coordinate :: word width inverseBase :: stack) output)
      (atState ((heap.set address (word width (count + 1))).set
        (inverseBase + count) (word width coordinate)
          (by simpa only [Array.size_set] using inverseValid)) (base + 20)
        count tableBase (count + 1) 1 (word width inverseBase :: stack) output)
      11 (7 + heap.size + stack.length + output.length) := by
  let firstHeap := heap.set address (word width (count + 1))
  let finalHeap := firstHeap.set (inverseBase + count) (word width coordinate)
    (by simpa only [firstHeap, Array.size_set] using inverseValid)
  let initial := atState heap (base + 9) 0 tableBase count address
    (word width coordinate :: word width inverseBase :: stack) output
  let one := atState heap (base + 10) 1 tableBase count address
    (word width coordinate :: word width inverseBase :: stack) output
  let two := atState heap (base + 11) (count + 1) tableBase count address
    (word width coordinate :: word width inverseBase :: stack) output
  let three := atState firstHeap (base + 12) (count + 1) tableBase count address
    (word width coordinate :: word width inverseBase :: stack) output
  let four := atState firstHeap (base + 13) coordinate tableBase count address
    (word width inverseBase :: stack) output
  let five := atState firstHeap (base + 14) coordinate tableBase count inverseBase stack output
  let six := atState firstHeap (base + 15) coordinate tableBase count inverseBase
    (word width inverseBase :: stack) output
  let seven := atState firstHeap (base + 16) coordinate tableBase count (inverseBase + count)
    (word width inverseBase :: stack) output
  let eight := atState finalHeap (base + 17) coordinate tableBase count (inverseBase + count)
    (word width inverseBase :: stack) output
  let nine := atState finalHeap (base + 18) count tableBase count (inverseBase + count)
    (word width inverseBase :: stack) output
  let ten := atState finalHeap (base + 19) count tableBase count 1
    (word width inverseBase :: stack) output
  let final := atState finalHeap (base + 20) count tableBase (count + 1) 1
    (word width inverseBase :: stack) output
  have countWord : (word width count).val = count := Nat.mod_eq_of_lt (by omega)
  have inverseWord : (word width inverseBase).val = inverseBase := Nat.mod_eq_of_lt (by omega)
  have inverseAddressWord : (word width (inverseBase + count)).val = inverseBase + count :=
    Nat.mod_eq_of_lt inverseFits
  have addressWord : (word width address).val = address := Nat.mod_eq_of_lt addressFits
  have oneWord : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have firstSize : firstHeap.size = heap.size := by simp [firstHeap]
  have finalSize : finalHeap.size = heap.size := by simp [finalHeap, firstSize]
  have step9 : programStep program initial = some one := by
    rw [fetched program initial (base + 9) (.constant 0 (word width 1)) rfl (by omega)
      (by simpa [code] using block 9 (by simp [code]))]
    change some (initial.advance.put 0 (word width 1)) = some one
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have step10 : programStep program one = some two := by
    rw [fetched program one (base + 10) (.add 0 2 0) rfl (by omega)
      (by simpa [code] using block 10 (by simp [code]))]
    change some (one.advance.put 0 (word width ((word width count).val + (word width 1).val))) = some two
    rw [countWord, oneWord, advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have step11 : programStep program two = some three := by
    rw [fetched program two (base + 11) (.store 3 0) rfl (by omega)
      (by simpa [code] using block 11 (by simp [code]))]
    change (if h : (word width (address)).val < heap.size then
      some { two.advance with heap := (heap.set (word width (address)).val
        (word width (count + 1))) } else none) = some three
    rw [addressWord, dite_eq_left (addressValid), advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  have step12 : programStep program three = some four := by
    rw [fetched program three (base + 12) (.pop 0) rfl (by omega)
      (by simpa [code] using block 12 (by simp [code]))]
    change some { three.advance.put 0 (word width coordinate) with stack := word width inverseBase :: stack } = some four
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
    rfl
  have step13 : programStep program four = some five := by
    rw [fetched program four (base + 13) (.pop 3) rfl (by omega)
      (by simpa [code] using block 13 (by simp [code]))]
    change some { four.advance.put 3 (word width inverseBase) with stack := stack } = some five
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
    rfl
  have step14 : programStep program five = some six := by
    rw [fetched program five (base + 14) (.push 3) rfl (by omega)
      (by simpa [code] using block 14 (by simp [code]))]
    change some { five.advance with stack := word width inverseBase :: stack } = some six
    rw [advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  have step15 : programStep program six = some seven := by
    rw [fetched program six (base + 15) (.add 3 3 2) rfl (by omega)
      (by simpa [code] using block 15 (by simp [code]))]
    change some (six.advance.put 3 (word width ((word width inverseBase).val + (word width count).val))) = some seven
    rw [inverseWord, countWord, advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have step16 : programStep program seven = some eight := by
    rw [fetched program seven (base + 16) (.store 3 0) rfl (by omega)
      (by simpa [code] using block 16 (by simp [code]))]
    change (if h : (word width (inverseBase + count)).val < firstHeap.size then
      some { seven.advance with heap := (firstHeap.set (word width (inverseBase + count)).val
        (word width (coordinate))) } else none) = some eight
    rw [inverseAddressWord, dite_eq_left (by simpa only [firstSize] using inverseValid), advance_at _ _ _ _ _ _ _ _ (by omega)]
    rfl
  have step17 : programStep program eight = some nine := by
    rw [fetched program eight (base + 17) (.copy 0 2) rfl (by omega)
      (by simpa [code] using block 17 (by simp [code]))]
    change some (eight.advance.put 0 (word width count)) = some nine
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put0_at]
  have step18 : programStep program nine = some ten := by
    rw [fetched program nine (base + 18) (.constant 3 (word width 1)) rfl (by omega)
      (by simpa [code] using block 18 (by simp [code]))]
    change some (nine.advance.put 3 (word width 1)) = some ten
    rw [advance_at _ _ _ _ _ _ _ _ (by omega), put3_at]
  have step19 : programStep program ten = some final := by
    rw [fetched program ten (base + 19) (.add 2 2 3) rfl (by omega)
      (by simpa [code] using block 19 (by simp [code]))]
    change some (ten.advance.put 2 (word width ((word width count).val + (word width 1).val))) = some final
    rw [countWord, oneWord, advance_at _ _ _ _ _ _ _ _ (by omega), put2_at]
  have firstTrace := Execution.cons step9 (Execution.cons step10
    (Execution.cons step11 (Execution.refl three)))
  have middleTrace := Execution.cons step12 (Execution.cons step13
    (Execution.cons step14 (Execution.cons step15 (Execution.refl seven))))
  have lastTrace := Execution.cons step16 (Execution.cons step17
    (Execution.cons step18 (Execution.cons step19 (Execution.refl final))))
  have joined := (firstTrace.append middleTrace).append lastTrace
  have initialWords : initial.liveWords = 7 + heap.size + stack.length + output.length := by
    simp [initial, firstSize, finalSize]; omega
  have oneWords : one.liveWords = 7 + heap.size + stack.length + output.length := by
    simp [one, firstSize, finalSize]; omega
  have twoWords : two.liveWords = 7 + heap.size + stack.length + output.length := by
    simp [two, firstSize, finalSize]; omega
  have threeWords : three.liveWords = 7 + heap.size + stack.length + output.length := by
    simp [three, firstSize, finalSize]; omega
  have fourWords : four.liveWords = 6 + heap.size + stack.length + output.length := by
    simp [four, firstSize, finalSize]; omega
  have fiveWords : five.liveWords = 5 + heap.size + stack.length + output.length := by
    simp [five, firstSize, finalSize]
  have sixWords : six.liveWords = 6 + heap.size + stack.length + output.length := by
    simp [six, firstSize, finalSize]; omega
  have sevenWords : seven.liveWords = 6 + heap.size + stack.length + output.length := by
    simp [seven, firstSize, finalSize]; omega
  have eightWords : eight.liveWords = 6 + heap.size + stack.length + output.length := by
    simp [eight, firstSize, finalSize]; omega
  have nineWords : nine.liveWords = 6 + heap.size + stack.length + output.length := by
    simp [nine, firstSize, finalSize]; omega
  have tenWords : ten.liveWords = 6 + heap.size + stack.length + output.length := by
    simp [ten, firstSize, finalSize]; omega
  have finalWords : final.liveWords = 6 + heap.size + stack.length + output.length := by
    simp [final, firstSize, finalSize]; omega
  simpa only [initialWords, oneWords, twoWords, threeWords, fourWords, fiveWords,
    sixWords, sevenWords, eightWords, nineWords, tenWords, finalWords,
    Nat.max_self,
    Nat.max_eq_left (show 5 + heap.size + stack.length + output.length ≤
      6 + heap.size + stack.length + output.length by omega),
    Nat.max_eq_left (show 6 + heap.size + stack.length + output.length ≤
      7 + heap.size + stack.length + output.length by omega),
    Nat.max_eq_right (show 5 + heap.size + stack.length + output.length ≤
      6 + heap.size + stack.length + output.length by omega),
    Nat.max_eq_right (show 6 + heap.size + stack.length + output.length ≤
      7 + heap.size + stack.length + output.length by omega), Nat.zero_add] using joined

/-- The complete repeated-coordinate call executes exactly nine fetched
instructions and returns the decoded ID without changing either stored region. -/
theorem touch_existing_execution (program : Program width 4) (heap : Array (Word width))
    (base coordinate tableBase count scratch encoded inverseBase : ℕ)
    (stack output : List (Word width))
    (addressFits : coordinate + tableBase < 2 ^ width)
    (addressValid : coordinate + tableBase < heap.size)
    (positive : 0 < encoded) (encodedFits : encoded < 2 ^ width)
    (stored : heap[coordinate + tableBase]'addressValid = word width encoded)
    (programFits : base + 20 < 2 ^ width)
    (block : BlockAt program base (code width base)) :
    Execution program
      (atState heap base coordinate tableBase count scratch (word width inverseBase :: stack) output)
      (atState heap (base + 20) (encoded - 1) tableBase count 0
        (word width inverseBase :: stack) output)
      9 (7 + heap.size + stack.length + output.length) := by
  have first := prefix_execution program heap base coordinate tableBase count scratch encoded
    (word width inverseBase :: stack) output addressFits addressValid encodedFits stored programFits block
  have nonzero : encoded ≠ 0 := Nat.ne_of_gt positive
  simp only [ite_eq_right nonzero] at first
  have last := existing_execution program heap base encoded tableBase count (coordinate + tableBase)
    coordinate (word width inverseBase :: stack) output positive encodedFits programFits block
  have joined := first.append last
  convert joined using 1 <;> simp only [List.length_cons, Nat.max_self] <;> omega

/-- The complete first-coordinate call executes exactly fifteen fetched
instructions, writes the actual slot/inverse cells and returns the old count
as its local ID. Its inverse-region base word remains on the caller stack. -/
theorem touch_fresh_execution (program : Program width 4) (heap : Array (Word width))
    (base coordinate tableBase count scratch inverseBase : ℕ)
    (stack output : List (Word width))
    (addressFits : coordinate + tableBase < 2 ^ width)
    (addressValid : coordinate + tableBase < heap.size)
    (countFits : count + 1 < 2 ^ width)
    (inverseFits : inverseBase + count < 2 ^ width)
    (inverseValid : inverseBase + count < heap.size)
    (unseen : heap[coordinate + tableBase]'addressValid = word width 0)
    (programFits : base + 20 < 2 ^ width)
    (block : BlockAt program base (code width base)) :
    Execution program
      (atState heap base coordinate tableBase count scratch (word width inverseBase :: stack) output)
      (atState ((heap.set (coordinate + tableBase) (word width (count + 1))).set
        (inverseBase + count) (word width coordinate)
          (by simpa only [Array.size_set] using inverseValid)) (base + 20)
        count tableBase (count + 1) 1 (word width inverseBase :: stack) output)
      15 (7 + heap.size + stack.length + output.length) := by
  have zeroFits : 0 < 2 ^ width := Nat.two_pow_pos width
  have first := prefix_execution program heap base coordinate tableBase count scratch 0
    (word width inverseBase :: stack) output addressFits addressValid zeroFits unseen programFits block
  simp only [ite_eq_left rfl] at first
  have last := fresh_execution program heap base coordinate tableBase count (coordinate + tableBase)
    inverseBase stack output addressFits addressValid countFits inverseFits inverseValid programFits block
  have joined := first.append last
  convert joined using 1 <;> simp only [List.length_cons, Nat.max_self] <;> omega

end Controller.Cost.ForestZeroTouch
