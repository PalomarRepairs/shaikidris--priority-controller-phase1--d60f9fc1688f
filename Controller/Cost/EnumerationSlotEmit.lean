module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationSlotCode

@[expose] public section

/-! Mask-selected unit emission in the four-register constructor. Literal
source reads and dictionary updates use the accepted R04 emitter; both mask
tests and the common return jump are charged in the actual fetched trace. -/
namespace Controller.Cost.EnumerationSlotEmit
open Controller.CNF Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroEmit Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroRows
open Controller.Cost.EnumerationSlotCode

theorem literal_return_execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (represented : Represented heap layout dictionary) (channels sourceEnd : Nat)
    (reference : Reference ambient) (stored : StoredReference heap channels sourceEnd reference)
    (base back input scratch : Nat) (stack output : List (Word width))
    (room : heap.size + 2 < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + (literalCode width base reference).length + 2 < 2 ^ width)
    (literalAt : BlockAt program base (literalCode width base reference))
    (jumpAt : BlockAt program (base + (literalCode width base reference).length)
      (ForestZeroAdmissibleCaller.jumpCode width back)) :
    ∃ ticks, ticks ≤ 25 ∧ Execution program
      (atState heap base input layout.tableBase dictionary.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      (atState (literalHeap heap layout dictionary (reference.coordinate, reference.positive)) back
        (touch dictionary reference.coordinate).2.1 layout.tableBase
        (touch dictionary reference.coordinate).1.coordinates.size 0
        (word width layout.inverseBase :: stack) output)
      ticks (8 + heap.size + stack.length + output.length) := by
  obtain ⟨ticks, time, emission⟩ := emit_literal_execution program heap layout dictionary represented
    channels sourceEnd reference stored base input scratch stack output room ambientFits (by omega) literalAt
  have returned := ForestZeroAdmissibleCaller.jump_execution program
    (literalHeap heap layout dictionary (reference.coordinate, reference.positive))
    (base + (literalCode width base reference).length) back
    (touch dictionary reference.coordinate).2.1 layout.tableBase
    (touch dictionary reference.coordinate).1.coordinates.size (if reference.positive then 1 else 0)
    (word width layout.inverseBase :: stack) output programFits jumpAt
  have trace := emission.append returned
  refine ⟨ticks + 2, by omega, ?_⟩
  have returnedPeak : 5 + (literalHeap heap layout dictionary (reference.coordinate, reference.positive)).size +
      (word width layout.inverseBase :: stack).length + output.length =
      8 + heap.size + stack.length + output.length := by
    simp only [literalHeap_size, List.length_cons]
    omega
  rw [returnedPeak, Nat.max_self] at trace
  exact trace

set_option maxHeartbeats 2000000 in
theorem execution (program : Program width 4) (heap : Array (Word width))
    (layout : Layout ambient heap.size) (dictionary : Dictionary ambient)
    (represented : Represented heap layout dictionary) (channels sourceEnd : Nat)
    (positive negative inactive : Reference ambient)
    (positiveChannel : positive.activity = false) (negativeChannel : negative.activity = false)
    (inactiveRoot : inactive.activity = true)
    (positiveStored : StoredReference heap channels sourceEnd positive)
    (negativeStored : StoredReference heap channels sourceEnd negative)
    (inactiveStored : StoredReference heap channels sourceEnd inactive)
    (base trueMask falseMask input scratch : Nat) (trueFlag falseFlag : Bool)
    (stack output : List (Word width)) (widthPositive : 0 < width)
    (trueFits : trueMask < 2 ^ width) (falseFits : falseMask < 2 ^ width)
    (trueValid : trueMask < heap.size) (falseValid : falseMask < heap.size)
    (trueCell : heap[trueMask]? = some (boolWord width trueFlag))
    (falseCell : heap[falseMask]? = some (boolWord width falseFlag))
    (room : heap.size + 2 < 2 ^ width) (ambientFits : ambient + 1 < 2 ^ width)
    (programFits : base + 90 < 2 ^ width)
    (block : BlockAt program base (code width base trueMask falseMask positive negative inactive)) :
    let reference := selected positive negative inactive trueFlag falseFlag
    ∃ ticks, ticks ≤ 31 ∧ Execution program
      (atState heap base input layout.tableBase dictionary.coordinates.size scratch
        (word width layout.inverseBase :: stack) output)
      (atState (literalHeap heap layout dictionary (reference.coordinate, reference.positive)) (base + 90)
        (touch dictionary reference.coordinate).2.1 layout.tableBase
        (touch dictionary reference.coordinate).1.coordinates.size 0
        (word width layout.inverseBase :: stack) output)
      ticks (8 + heap.size + stack.length + output.length) := by
  dsimp only
  obtain ⟨trueAt, positiveAt, positiveJump, falseAt, negativeAt, negativeJump, inactiveAt, inactiveJump⟩ :=
    blocks program positive negative inactive positiveChannel negativeChannel inactiveRoot block
  have positiveLength : (literalCode width (base + 3) positive).length = 25 := by
    simp [literalCode_length, readCode_length, positiveChannel]
  have negativeLength : (literalCode width (base + 33) negative).length = 25 := by
    simp [literalCode_length, readCode_length, negativeChannel]
  have inactiveLength : (literalCode width (base + 60) inactive).length = 28 := by
    simp [literalCode_length, readCode_length, inactiveRoot]
  have first := mask_execution program heap base trueMask (base + 30) input layout.tableBase
    dictionary.coordinates.size scratch trueFlag (word width layout.inverseBase :: stack) output
    widthPositive trueFits trueValid trueCell (by omega) trueAt
  cases trueFlag with
  | true =>
    simp only [ite_true] at first
    obtain ⟨ticks, time, emitted⟩ := literal_return_execution program heap layout dictionary represented
      channels sourceEnd positive positiveStored (base + 3) (base + 90) 1 scratch stack output room ambientFits
      (by rw [positiveLength]; omega) positiveAt
      (by simpa only [positiveLength, Nat.add_assoc, Nat.reduceAdd] using positiveJump)
    refine ⟨3 + ticks, by omega, ?_⟩
    simpa only [selected, ite_true, List.length_cons,
      Nat.max_eq_right (by omega : 5 + heap.size + (stack.length + 1) + output.length ≤
        8 + heap.size + stack.length + output.length)] using first.append emitted
  | false =>
    simp only [Bool.false_eq_true, ite_false] at first
    have second := mask_execution program heap (base + 30) falseMask (base + 60) 0 layout.tableBase
      dictionary.coordinates.size scratch falseFlag (word width layout.inverseBase :: stack) output
      widthPositive falseFits falseValid falseCell (by omega) falseAt
    have tests := first.append second
    simp only [List.length_cons, Nat.max_self, Nat.reduceAdd] at tests
    cases falseFlag with
    | true =>
      simp only [ite_true] at tests
      obtain ⟨ticks, time, emitted⟩ := literal_return_execution program heap layout dictionary represented
        channels sourceEnd negative negativeStored (base + 33) (base + 90) 1 scratch stack output room ambientFits
        (by rw [negativeLength]; omega) negativeAt
        (by simpa only [negativeLength, Nat.add_assoc, Nat.reduceAdd] using negativeJump)
      refine ⟨6 + ticks, by omega, ?_⟩
      simpa only [selected, Bool.false_eq_true, ite_false, ite_true,
        Nat.max_eq_right (by omega : 5 + heap.size + (stack.length + 1) + output.length ≤
          8 + heap.size + stack.length + output.length)] using tests.append emitted
    | false =>
      simp only [Bool.false_eq_true, ite_false] at tests
      obtain ⟨ticks, time, emitted⟩ := literal_return_execution program heap layout dictionary represented
        channels sourceEnd inactive inactiveStored (base + 60) (base + 90) 0 scratch stack output room ambientFits
        (by rw [inactiveLength]; omega) inactiveAt
        (by simpa only [inactiveLength, Nat.add_assoc, Nat.reduceAdd] using inactiveJump)
      refine ⟨6 + ticks, by omega, ?_⟩
      simpa only [selected, Bool.false_eq_true, ite_false,
        Nat.max_eq_right (by omega : 5 + heap.size + (stack.length + 1) + output.length ≤
          8 + heap.size + stack.length + output.length)] using tests.append emitted

end Controller.Cost.EnumerationSlotEmit
