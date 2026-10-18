module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeGateConditional

@[expose] public section

/-! Native AND/OR input lists are scanned occurrence by occurrence. The fetched
fold preserves the heap and all retained buffers, including empty input lists. -/
namespace Controller.Cost.NativeGateFold
open Controller.Cost.GateProgram Controller.CNF

def result (values : Fin variableCount → Bool) (replacement : Bool) :
    List (Literal (Fin variableCount)) → Bool → Bool
  | [], accumulator => accumulator
  | literal :: rest, accumulator =>
      result values replacement rest (if literalValue values literal then replacement else accumulator)

def code (width base : Nat) (replacement : Bool) (entry : Nat) :
    List (Literal (Fin variableCount)) → List (Instruction width 4)
  | [] => []
  | literal :: rest => NativeGateConditional.code width base entry literal replacement ++
      code width base replacement (entry + 6) rest

@[simp] theorem code_length (width base : Nat) (replacement : Bool) (entry : Nat)
    (inputs : List (Literal (Fin variableCount))) :
    (code width base replacement entry inputs).length = 6 * inputs.length := by
  induction inputs generalizing entry with
  | nil => rfl
  | cons literal rest ih => simp [code, ih]; omega

def Stored (heap : Array (Word width)) (values : Fin variableCount → Bool) (base : Nat)
    (inputs : List (Literal (Fin variableCount))) : Prop :=
  ∀ literal ∈ inputs, ∃ valid : base + literal.1.val < heap.size,
    heap[base + literal.1.val]'valid = boolWord width (values literal.1)

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (values : Fin variableCount → Bool) (inputs : List (Literal (Fin variableCount)))
    (accumulator replacement : Bool) (base entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 6 * inputs.length < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (stored : Stored state.heap values base inputs)
    (held : state.reg 3 = boolWord width accumulator)
    (physical : BlockAt resident entry (code width base replacement entry inputs)) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 6 * inputs.length ∧
      final.reg 3 = boolWord width (result values replacement inputs accumulator) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 6 * inputs.length) ∧ final.halted = false := by
  induction inputs generalizing state accumulator entry with
  | nil =>
    refine ⟨state, 0, Execution.refl state, by simp, held, rfl, rfl, rfl, ?_, running⟩
    simpa using position
  | cons literal rest ih =>
    obtain ⟨valid, cell⟩ := stored literal (by simp)
    have firstBlock : BlockAt resident entry
        (NativeGateConditional.code width base entry literal replacement) :=
      BlockAt.prefix _ _ _ _ physical
    obtain ⟨middle, firstTicks, firstTrace, firstBound, middleHeld, middleHeap,
      middleStack, middleOutput, middlePC, middleRunning⟩ :=
      NativeGateConditional.execution resident state values literal accumulator replacement base entry
        position running (by simp only [List.length_cons] at room; omega) boolFits heapFits
        valid cell held firstBlock
    have restBlock : BlockAt resident (entry + 6) (code width base replacement (entry + 6) rest) := by
      simpa only [NativeGateConditional.code_length] using BlockAt.suffix _ _ _ _ physical
    have restStored : Stored middle.heap values base rest := by
      rw [middleHeap]
      intro item membership
      exact stored item (by simp [membership])
    obtain ⟨final, restTicks, restTrace, restBound, finalHeld, finalHeap,
      finalStack, finalOutput, finalPC, finalRunning⟩ :=
      ih middle (if literalValue values literal then replacement else accumulator) (entry + 6)
        middlePC middleRunning (by simp only [List.length_cons] at room; omega)
        (by simpa only [middleHeap] using heapFits) restStored middleHeld restBlock
    have middleLive : middle.liveWords = state.liveWords := by
      simp [State.liveWords, middleHeap, middleStack, middleOutput]
    refine ⟨final, firstTicks + restTicks, ?_, ?_, finalHeld,
      finalHeap.trans middleHeap, finalStack.trans middleStack, finalOutput.trans middleOutput,
      ?_, finalRunning⟩
    · simpa only [middleLive, Nat.max_self] using firstTrace.append restTrace
    · simp only [List.length_cons]; omega
    · convert finalPC using 1 <;> congr 1 <;> simp only [List.length_cons] <;> omega

theorem result_or (values : Fin variableCount → Bool)
    (inputs : List (Literal (Fin variableCount))) (accumulator : Bool) :
    result values true inputs accumulator = (accumulator || inputs.any (literalValue values)) := by
  induction inputs generalizing accumulator with
  | nil => simp [result]
  | cons literal rest ih =>
    simp only [result, List.any_cons, ih]
    cases accumulator <;> cases literalValue values literal <;> simp

theorem result_and (values : Fin variableCount → Bool)
    (inputs : List (Literal (Fin variableCount))) (accumulator : Bool) :
    result values false (inputs.map negate) accumulator = (accumulator && inputs.all (literalValue values)) := by
  induction inputs generalizing accumulator with
  | nil => simp [result]
  | cons literal rest ih =>
    simp only [List.map_cons, result, literalValue_negate, List.all_cons, ih]
    cases accumulator <;> cases literalValue values literal <;> simp

end Controller.Cost.NativeGateFold
