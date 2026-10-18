module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedChannelRewrite
public import Controller.Cost.SharedWitnessPark

@[expose] public section

/-! The healthy reference is preserved while a single baseline mask replaces the channel table. -/
namespace Controller.Cost.SharedBaselineLoad
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.ForestInputStored

@[irreducible] def code (width base n count entry done : Nat) : Program width 8 :=
  (SharedWitnessPark.code width count).toArray ++
    ((SharedChannelRewrite.code width base (List.finRange n)).toArray ++
      SharedWitnessRestore.preparedCode width (entry + 2 * count + 3 * n) done (base + n) count)

@[simp] theorem code_size (width base n count entry done : Nat) :
    (code width base n count entry done).size = 2 * count + 3 * n + 17 := by unfold code; simp; omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (retained : Array (Word width)) (healthy baseline : Fin n → Bool)
    (references suffix : List (Word width)) (entry done : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 * references.length + 3 * n + 17 < 2 ^ width)
    (positive : 0 < retained.size + n)
    (capacity : retained.size + n + references.length < 2 ^ width)
    (heapStored : state.heap = withValues retained healthy)
    (input : state.stack = references ++ (List.finRange n).map (fun channel => boolWord width (baseline channel)) ++ suffix)
    (physical : CodeAt resident entry (code width retained.size n references.length entry done)) :
    ∃ final peak, Execution resident state final (12 * references.length + 3 * n + 9) peak ∧
      peak ≤ state.liveWords + references.length ∧
      final.heap = withValues retained baseline ∧ final.stack = references ++ suffix ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = state.reg 4 := by
  have all := physical
  unfold code at all
  have parkCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  have parkBlock : SharedRootRead.BlockAt resident entry (SharedWitnessPark.code width references.length) := by
    intro offset bound
    simpa using parkCode ⟨offset, by simpa using bound⟩
  obtain ⟨parked, parkTrace, parkedHeap, parkedStack, parkedOutput, parkedPC, parkedRunning, parkedHead⟩ :=
    SharedWitnessPark.execution resident state references
      ((List.finRange n).map (fun channel => boolWord width (baseline channel)) ++ suffix) entry
      position running (by omega) (by rw [heapStored, withValues_size]; exact capacity)
      (by simpa only [List.append_assoc] using input) parkBlock
  have restCode : CodeAt resident (entry + 2 * references.length)
      ((SharedChannelRewrite.code width retained.size (List.finRange n)).toArray ++
        SharedWitnessRestore.preparedCode width (entry + 2 * references.length + 3 * n)
          done (retained.size + n) references.length) := by
    simpa using tailCode
  have rewriteCode := RawSharedOrdered.takePrefix resident (entry + 2 * references.length) _ _ restCode
  have restoreCode := RawSharedOrdered.takeSuffix resident (entry + 2 * references.length) _ _ restCode
  have rewriteBlock : SharedRootRead.BlockAt resident (entry + 2 * references.length)
      (SharedChannelRewrite.code width retained.size (List.finRange n)) := by
    intro offset bound
    simpa using rewriteCode ⟨offset, by simpa using bound⟩
  obtain ⟨loaded, loadTrace, loadedHeap, loadedStack, loadedOutput, loadedPC, loadedRunning, loadedHead⟩ :=
    SharedChannelRewrite.execution resident parked retained references.toArray healthy baseline
      (List.finRange n) suffix (entry + 2 * references.length) parkedPC parkedRunning
      (by simpa using (show entry + 2 * references.length + 3 * n < 2 ^ width from by omega))
      (by omega) (by simpa only [heapStored] using parkedHeap) parkedStack rewriteBlock
  obtain ⟨final, restoreTrace, finalHeap, finalStack, finalOutput, finalPC,
    finalRunning, finalHead, finalOther⟩ :=
    SharedWitnessRestore.prepared_execution resident loaded (withValues retained baseline) references
      (entry + 2 * references.length + 3 * n) done (by simpa using loadedPC) loadedRunning
      (by omega) (by simpa using positive) (by simpa using capacity)
      (by simpa using loadedHeap) (by simpa using restoreCode)
  have parkedLive : parked.liveWords = state.liveWords := by
    simp only [State.liveWords, parkedHeap, parkedStack, parkedOutput, Array.size_append,
      List.size_toArray, input, List.length_append]
    omega
  have loadedLive : loaded.liveWords + n = state.liveWords := by
    simp only [State.liveWords, loadedHeap, SharedChannelRewrite.replace_all, Array.size_append,
      withValues_size, List.size_toArray, loadedStack, loadedOutput, parkedOutput,
      heapStored, withValues_size, input, List.length_append, List.length_map, List.length_finRange]
    omega
  have joined := parkTrace.append (loadTrace.append restoreTrace)
  simp only [List.length_finRange] at joined
  refine ⟨final, max state.liveWords (max parked.liveWords (loaded.liveWords + references.length)),
    ?_, ?_, finalHeap, ?_, finalOutput.trans (loadedOutput.trans parkedOutput), finalPC, finalRunning,
    finalHead.trans (loadedHead.trans (parkedHead 4 (by decide)))⟩
  · convert joined using 1 <;> omega
  · apply Nat.max_le.mpr
    constructor
    · omega
    · apply Nat.max_le.mpr
      constructor <;> omega
  · simpa only [loadedStack] using finalStack

end Controller.Cost.SharedBaselineLoad
