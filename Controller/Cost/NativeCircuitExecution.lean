module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeGateExecution

@[expose] public section

/-! Native acyclic circuits execute their gates in allocation order against one
resident assignment table. The trace appends each evaluated output exactly once. -/
namespace Controller.Cost.NativeCircuitExecution
open Controller.Cost.GateProgram Controller.CNF

def TableStored (heap : Array (Word width)) (base : Nat) (values : Fin variableCount → Bool) : Prop :=
  base + variableCount = heap.size ∧
    ∀ index : Fin variableCount, ∃ valid : base + index.val < heap.size,
      heap[base + index.val]'valid = boolWord width (values index)

theorem TableStored.push (heap : Array (Word width)) (base : Nat)
    (values : Fin variableCount → Bool) (stored : TableStored heap base values)
    (phase value : Bool) :
    TableStored (heap.push (boolWord width (value == phase))) base
      (extendAssignment values phase value) := by
  have atEnd := stored.1
  refine ⟨by simp only [Array.size_push]; omega, ?_⟩
  intro index
  refine Fin.lastCases ?_ (fun old => ?_) index
  · have valid : base + (Fin.last variableCount).val <
        (heap.push (boolWord width (value == phase))).size := by
      simp only [Fin.val_last, Array.size_push]
      omega
    refine ⟨valid, ?_⟩
    simp only [Fin.val_last, extendAssignment_last]
    simpa only [atEnd] using (Array.getElem_push_eq (xs := heap) (x := boolWord width (value == phase)))
  · obtain ⟨valid, cell⟩ := stored.2 old
    refine ⟨by simp only [Fin.val_castSucc, Array.size_push]; omega, ?_⟩
    simp only [Fin.val_castSucc, extendAssignment_old]
    rw [Array.getElem_push_lt valid]
    exact cell

def code (width base entry : Nat) : AcyclicCircuit rootCount variableCount → List (Instruction width 4)
  | .roots => []
  | .snoc previous gate phase => code width base entry previous ++
      NativeGateExecution.code width base (entry + (code width base entry previous).length) phase gate

def inputOccurrences : AcyclicCircuit rootCount variableCount → Nat
  | .roots => 0
  | .snoc previous gate _ => inputOccurrences previous + gate.inputs.length

theorem code_length_le (width base entry : Nat) (circuit : AcyclicCircuit rootCount variableCount) :
    (code width base entry circuit).length ≤ 13 * (circuit.gateCount + inputOccurrences circuit) := by
  induction circuit with
  | roots => rfl
  | snoc previous gate phase ih =>
    have current := NativeGateExecution.code_length_le width base
      (entry + (code width base entry previous).length) phase gate
    simp only [code, List.length_append, AcyclicCircuit.gateCount, inputOccurrences]
    omega

set_option maxHeartbeats 3000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (circuit : AcyclicCircuit rootCount variableCount) (roots : Fin rootCount → Bool)
    (base entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + (code width base entry circuit).length < 2 ^ width)
    (boolFits : 1 < 2 ^ width) (tableRoom : base + variableCount < 2 ^ width)
    (stored : TableStored state.heap base roots)
    (physical : BlockAt resident entry (code width base entry circuit)) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + circuit.gateCount) ∧
      ticks ≤ (code width base entry circuit).length ∧
      TableStored final.heap base (circuit.evaluate roots) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + (code width base entry circuit).length) ∧ final.halted = false := by
  induction circuit with
  | roots =>
    refine ⟨state, 0, ?_, by simp [code], stored, rfl, rfl, ?_, running⟩
    · simpa only [AcyclicCircuit.gateCount, Nat.add_zero] using Execution.refl (p := resident) state
    · simpa only [code, List.length_nil, Nat.add_zero] using position
  | @snoc variableCount previous gate phase ih =>
    have previousBlock : BlockAt resident entry (code width base entry previous) :=
      BlockAt.prefix _ _ _ _ physical
    obtain ⟨middle, previousTicks, previousTrace, previousBound, previousTable,
      middleStack, middleOutput, middlePC, middleRunning⟩ :=
      ih (by simp only [code, List.length_append] at room; omega) (by omega) previousBlock
    have gateBlock : BlockAt resident (entry + (code width base entry previous).length)
        (NativeGateExecution.code width base (entry + (code width base entry previous).length) phase gate) :=
      BlockAt.suffix _ _ _ _ physical
    have gateStored : NativeGateFold.Stored middle.heap (previous.evaluate roots) base gate.inputs := by
      intro literal _
      exact previousTable.2 literal.1
    obtain ⟨final, gateTicks, gateTrace, gateBound, finalHeap,
      finalStack, finalOutput, finalPC, finalRunning⟩ :=
      NativeGateExecution.execution resident middle (previous.evaluate roots) gate phase base
        (entry + (code width base entry previous).length) middlePC middleRunning
        (by simpa only [code, List.length_append, Nat.add_assoc] using room) boolFits
        (by have size := previousTable.1; omega) gateStored gateBlock
    have middleLive : middle.liveWords = state.liveWords + previous.gateCount := by
      have sizes := previous.variable_count
      have initialSize := stored.1
      have middleSize := previousTable.1
      simp only [State.liveWords, middleStack, middleOutput]
      omega
    have finalTable : TableStored final.heap base ((previous.snoc gate phase).evaluate roots) := by
      rw [finalHeap]
      exact TableStored.push middle.heap base (previous.evaluate roots) previousTable phase
        (gate.eval (previous.evaluate roots))
    refine ⟨final, previousTicks + gateTicks, ?_, ?_, finalTable,
      finalStack.trans middleStack, finalOutput.trans middleOutput, ?_, finalRunning⟩
    · have peakEq : max (state.liveWords + previous.gateCount) (middle.liveWords + 1) =
          state.liveWords + (previous.gateCount + 1) := by rw [middleLive]; omega
      simpa only [peakEq, AcyclicCircuit.gateCount] using previousTrace.append gateTrace
    · simpa only [code, List.length_append] using Nat.add_le_add previousBound gateBound
    · simpa only [code, List.length_append, Nat.add_assoc] using finalPC

end Controller.Cost.NativeCircuitExecution
