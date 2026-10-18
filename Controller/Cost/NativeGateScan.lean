module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.NativeGateFold
public import Controller.Cost.NativeGateStore

@[expose] public section

/-! Native scanning gates initialize an accumulator, scan every signed input
occurrence and append the signed result. Empty scans implement constants. -/
namespace Controller.Cost.NativeGateScan
open Controller.Cost.GateProgram Controller.CNF

def code (width base entry : Nat) (inputs : List (Literal (Fin variableCount)))
    (initial replacement phase : Bool) : List (Instruction width 4) :=
  [.constant 3 (boolWord width initial)] ++
    (NativeGateFold.code width base replacement (entry + 1) inputs ++ NativeGateStore.code width phase)

@[simp] theorem code_length (width base entry : Nat) (inputs : List (Literal (Fin variableCount)))
    (initial replacement phase : Bool) :
    (code width base entry inputs initial replacement phase).length = 6 * inputs.length + 4 := by
  simp [code]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 4) (state : State width 4)
    (values : Fin variableCount → Bool) (inputs : List (Literal (Fin variableCount)))
    (initial replacement phase : Bool) (base entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 6 * inputs.length + 4 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (stored : NativeGateFold.Stored state.heap values base inputs)
    (physical : BlockAt resident entry (code width base entry inputs initial replacement phase)) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + 1) ∧
      ticks ≤ 6 * inputs.length + 4 ∧
      final.heap = state.heap.push
        (boolWord width (NativeGateFold.result values replacement inputs initial == phase)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 6 * inputs.length + 4) ∧ final.halted = false := by
  let first := state.advance.put 3 (boolWord width initial)
  have firstFetch : resident[entry]? = some (.constant 3 (boolWord width initial)) := by
    simpa [code] using physical 0 (by simp [code])
  have firstTrace : Execution resident state first 1 state.liveWords :=
    NativeGateOps.put_execution resident state (.constant 3 (boolWord width initial)) entry 3 _
      position (by omega) firstFetch (by simp [step, running])
  have firstPC : first.pc = word width (entry + 1) := by
    simpa [first, State.put] using NativeGateOps.advance_pc state entry position (by omega)
  have firstLive : first.liveWords = state.liveWords := by
    simp [first, State.advance, State.put, State.liveWords]
  have restBlock : BlockAt resident (entry + 1)
      (NativeGateFold.code width base replacement (entry + 1) inputs ++ NativeGateStore.code width phase) := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using BlockAt.suffix _ _ _ _ physical
  have foldBlock := BlockAt.prefix _ _ _ _ restBlock
  obtain ⟨folded, foldTicks, foldTrace, foldBound, foldedHeld, foldedHeap,
    foldedStack, foldedOutput, foldedPC, foldedRunning⟩ :=
    NativeGateFold.execution resident first values inputs initial replacement base (entry + 1)
      firstPC running (by omega) boolFits heapFits stored
      (by simp [first, State.put]) foldBlock
  have storeBlock : BlockAt resident (entry + 1 + 6 * inputs.length)
      (NativeGateStore.code width phase) := by
    simpa only [NativeGateFold.code_length] using BlockAt.suffix _ _ _ _ restBlock
  obtain ⟨final, storeTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    NativeGateStore.execution resident folded (NativeGateFold.result values replacement inputs initial)
      phase (entry + 1 + 6 * inputs.length) foldedPC foldedRunning (by omega) boolFits
      (by simpa [foldedHeap, first, State.advance, State.put] using heapFits) foldedHeld storeBlock
  have foldedLive : folded.liveWords = state.liveWords := by
    simp [State.liveWords, foldedHeap, foldedStack, foldedOutput, first, State.advance, State.put]
  refine ⟨final, 1 + foldTicks + 3, ?_, by omega, ?_, ?_, ?_, ?_, finalRunning⟩
  · simpa only [firstLive, foldedLive, Nat.max_self, Nat.max_eq_right (Nat.le_succ _)] using
      (firstTrace.append foldTrace).append storeTrace
  · simpa [foldedHeap, first, State.advance, State.put] using finalHeap
  · simpa [foldedStack, first, State.advance, State.put] using finalStack
  · simpa [foldedOutput, first, State.advance, State.put] using finalOutput
  · rw [finalPC]
    congr 1
    omega

theorem or_execution (resident : Program width 4) (state : State width 4)
    (values : Fin variableCount → Bool) (inputs : List (Literal (Fin variableCount))) (phase : Bool)
    (base entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 6 * inputs.length + 4 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (stored : NativeGateFold.Stored state.heap values base inputs)
    (physical : BlockAt resident entry (code width base entry inputs false true phase)) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + 1) ∧
      ticks ≤ 6 * inputs.length + 4 ∧
      final.heap = state.heap.push (boolWord width (inputs.any (literalValue values) == phase)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 6 * inputs.length + 4) ∧ final.halted = false := by
  simpa only [NativeGateFold.result_or, Bool.false_or] using
    execution resident state values inputs false true phase base entry position running room boolFits heapFits stored physical

theorem and_execution (resident : Program width 4) (state : State width 4)
    (values : Fin variableCount → Bool) (inputs : List (Literal (Fin variableCount))) (phase : Bool)
    (base entry : Nat) (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 6 * inputs.length + 4 < 2 ^ width) (boolFits : 1 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width)
    (stored : NativeGateFold.Stored state.heap values base inputs)
    (physical : BlockAt resident entry (code width base entry (inputs.map negate) true false phase)) :
    ∃ final ticks, Execution resident state final ticks (state.liveWords + 1) ∧
      ticks ≤ 6 * inputs.length + 4 ∧
      final.heap = state.heap.push (boolWord width (inputs.all (literalValue values) == phase)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 6 * inputs.length + 4) ∧ final.halted = false := by
  have negatedStored : NativeGateFold.Stored state.heap values base (inputs.map negate) := by
    intro literal membership
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp membership
    exact stored original originalMember
  simpa only [List.length_map, NativeGateFold.result_and, Bool.true_and] using
    execution resident state values (inputs.map negate) true false phase base entry position running
      (by simpa only [List.length_map] using room) boolFits heapFits negatedStored physical

end Controller.Cost.NativeGateScan
