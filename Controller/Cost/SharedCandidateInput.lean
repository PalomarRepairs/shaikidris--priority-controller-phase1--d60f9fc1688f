module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedWitnessPark

@[expose] public section

/-! A candidate constraint word is fetched beneath the retained witness vector. -/
namespace Controller.Cost.SharedCandidateInput
open Controller.Cost.RawTransferLoops

def code (width entry done heapSize count : Nat) : Program width 8 :=
  (SharedWitnessPark.code width count).toArray ++
    (#[.pop 2] ++ SharedWitnessRestore.preparedCode width (entry + 2 * count + 1) done heapSize count)

@[simp] theorem code_size (width entry done heapSize count : Nat) :
    (code width entry done heapSize count).size = 2 * count + 18 := by simp [code]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (witnesses suffix : List (Word width)) (value : Word width) (entry done : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 * witnesses.length + 18 < 2 ^ width)
    (positive : 0 < state.heap.size) (heapFits : state.heap.size + witnesses.length < 2 ^ width)
    (input : state.stack = witnesses ++ value :: suffix)
    (physical : CodeAt resident entry (code width entry done state.heap.size witnesses.length)) :
    ∃ final peak, Execution resident state final (12 * witnesses.length + 10) peak ∧
      peak ≤ state.liveWords + witnesses.length ∧ final.heap = state.heap ∧
      final.stack = witnesses ++ suffix ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.reg 2 = value ∧ final.reg 4 = state.reg 4 := by
  have all := physical
  unfold code at all
  have parkCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tail := RawSharedOrdered.takeSuffix resident entry _ _ all
  have parkBlock : SharedRootRead.BlockAt resident entry (SharedWitnessPark.code width witnesses.length) := by
    intro offset bound
    simpa using parkCode ⟨offset, by simpa using bound⟩
  obtain ⟨parked, parkTrace, parkedHeap, parkedStack, parkedOutput, parkedPC, parkedRunning, parkedFrame⟩ :=
    SharedWitnessPark.execution resident state witnesses (value :: suffix) entry position running
      (by omega) heapFits input parkBlock
  have restCode : CodeAt resident (entry + 2 * witnesses.length)
      (#[.pop 2] ++ SharedWitnessRestore.preparedCode width
        (entry + 2 * witnesses.length + 1) done state.heap.size witnesses.length) := by
    simpa only [List.size_toArray, SharedWitnessPark.code_length] using tail
  have popCode := RawSharedOrdered.takePrefix resident (entry + 2 * witnesses.length) _ _ restCode
  have restoreCode := RawSharedOrdered.takeSuffix resident (entry + 2 * witnesses.length) _ _ restCode
  let popped := { parked.advance.put 2 value with stack := suffix }
  have transition : programStep resident parked = some popped := by
    rw [fetched resident parked (entry + 2 * witnesses.length) _ parkedPC (by omega)
      (show resident[entry + 2 * witnesses.length]? = some (.pop 2) by
        simpa using popCode ⟨0, by simp⟩)]
    simp [step, parkedRunning, parkedStack, popped]
  have poppedPC : popped.pc = word width (entry + 2 * witnesses.length + 1) :=
    advance_position parked parkedPC (by omega)
  have parkedLive : parked.liveWords = state.liveWords := by
    simp only [State.liveWords, parkedHeap, parkedStack, parkedOutput, Array.size_append,
      List.size_toArray, input, List.length_append, List.length_cons]
    omega
  have poppedLive : popped.liveWords + 1 = state.liveWords := by
    simp only [popped, State.liveWords, State.advance, State.put, parkedHeap,
      parkedOutput, Array.size_append, List.size_toArray, input, List.length_append, List.length_cons]
    omega
  have popTrace : Execution resident parked popped 1 parked.liveWords := by
    have trace := Execution.cons transition (Execution.refl popped)
    have smaller : popped.liveWords ≤ parked.liveWords := by omega
    simpa only [Nat.zero_add, Nat.max_eq_left smaller] using trace
  obtain ⟨final, restoreTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame, finalBit⟩ :=
    SharedWitnessRestore.prepared_execution resident popped state.heap witnesses
      (entry + 2 * witnesses.length + 1) done poppedPC parkedRunning (by omega)
      positive heapFits parkedHeap (by simpa using restoreCode)
  have joined := parkTrace.append (popTrace.append restoreTrace)
  have timeEq : 2 * witnesses.length + (1 + (10 * witnesses.length + 9)) =
      12 * witnesses.length + 10 := by omega
  rw [timeEq] at joined
  refine ⟨final, max state.liveWords (max parked.liveWords (popped.liveWords + witnesses.length)),
    joined, ?_, finalHeap, finalStack, finalOutput.trans parkedOutput, finalPC, finalRunning, ?_, ?_⟩
  · rw [parkedLive]
    apply Nat.max_le.mpr
    constructor
    · omega
    · apply Nat.max_le.mpr
      constructor <;> omega
  · simpa [popped, State.put] using finalBit
  · exact finalFrame.trans (by simpa [popped, State.advance, State.put] using parkedFrame 4 (by decide))

end Controller.Cost.SharedCandidateInput
