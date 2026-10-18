module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedTagCompare

@[expose] public section

/-! Healthy and candidate root tags select the zero query, next root or true witness branch. -/
namespace Controller.Cost.SharedRootClassify
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width n entry zeroQuery nextRoot : Nat) : Program width 8 :=
  SharedTagCompare.code width (entry + 5) (n + 1) 2 ++
    (#[.constant 0 (word width 0), .branchZero 0 (word width zeroQuery)] ++
      SharedTagCompare.code width nextRoot (n + 1) 4)

@[simp] theorem code_size (width n entry zeroQuery nextRoot : Nat) :
    (code width n entry zeroQuery nextRoot).size = 8 := by simp [code]

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (n entry zeroQuery nextRoot : Nat) (target : Fin n) (healthy : Bool) (candidate : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 8 < 2 ^ width) (capacity : n + 1 < 2 ^ width)
    (healthyHeld : state.reg 2 = if healthy then word width target.val else word width (n + 1))
    (candidateHeld : state.reg 4 = candidate)
    (physical : CodeAt resident entry (code width n entry zeroQuery nextRoot)) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 6 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if healthy then zeroQuery else
        if candidate = word width (n + 1) then nextRoot else entry + 8) ∧
      final.halted = false ∧ final.reg 4 = candidate ∧ final.reg 3 = state.reg 3 ∧
      (∀ register : Fin 8, register ≠ 0 → final.reg register = state.reg register) := by
  have all := physical
  unfold code at all
  have healthyCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  have restCode : CodeAt resident (entry + 3)
      (#[.constant 0 (word width 0), .branchZero 0 (word width zeroQuery)] ++
        SharedTagCompare.code width nextRoot (n + 1) 4) := by simpa using tailCode
  have jumpCode := RawSharedOrdered.takePrefix resident (entry + 3) _ _ restCode
  have candidateCode := RawSharedOrdered.takeSuffix resident (entry + 3) _ _ restCode
  cases healthy with
  | false =>
    obtain ⟨ready, healthyTrace, readyHeap, readyStack, readyOutput, readyPC, readyRunning, readyFrame⟩ :=
      SharedTagCompare.execution resident state entry (entry + 5) (n + 1) (n + 1) 2 (by decide)
        position running (by omega) capacity capacity (by simpa using healthyHeld) healthyCode
    have candidateWord : word width candidate.val = candidate := by
      apply Fin.ext; exact Nat.mod_eq_of_lt candidate.isLt
    obtain ⟨final, candidateTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
      SharedTagCompare.execution resident ready (entry + 5) nextRoot (n + 1) candidate.val 4 (by decide)
        (by simpa using readyPC) readyRunning (by omega) capacity candidate.isLt
        (by rw [candidateWord]; exact (readyFrame 4 (by decide)).trans candidateHeld)
        (by simpa [Nat.add_assoc] using candidateCode)
    have readyLive : ready.liveWords = state.liveWords := by simp only [State.liveWords, readyHeap, readyStack, readyOutput]
    have joined := healthyTrace.append candidateTrace
    rw [readyLive, Nat.max_self] at joined
    have equal : candidate.val = n + 1 ↔ candidate = word width (n + 1) := by
      constructor
      · intro equal; rw [← candidateWord, equal]
      · intro equal; rw [equal]; exact Nat.mod_eq_of_lt capacity
    refine ⟨final, 6, by simpa using joined, by decide, finalHeap.trans readyHeap,
      finalStack.trans readyStack, finalOutput.trans readyOutput, ?_, finalRunning,
      (finalFrame 4 (by decide)).trans ((readyFrame 4 (by decide)).trans candidateHeld),
      (finalFrame 3 (by decide)).trans (readyFrame 3 (by decide)),
      fun register different => (finalFrame register different).trans (readyFrame register different)⟩
    simpa only [Bool.false_eq_true, ite_false, equal, Nat.add_assoc, Nat.reduceAdd] using finalPC
  | true =>
    obtain ⟨ready, healthyTrace, readyHeap, readyStack, readyOutput, readyPC, readyRunning, readyFrame⟩ :=
      SharedTagCompare.execution resident state entry (entry + 5) (n + 1) target.val 2 (by decide)
        position running (by omega) capacity (by omega) (by simpa using healthyHeld) healthyCode
    have readyPosition : ready.pc = word width (entry + 3) := by
      simpa only [ite_eq_right (by omega : target.val ≠ n + 1)] using readyPC
    obtain ⟨zeroed, zeroTrace, zeroPC, zeroValue, zeroHeap, zeroStack, zeroOutput, zeroRunning, zeroFrame⟩ :=
      SharedEvaluationReclaim.constant_execution resident (entry + 3) 0 0 ready readyPosition readyRunning
        (by omega) (by simpa using jumpCode ⟨0, by simp⟩)
    let final := { zeroed.advance with pc := word width zeroQuery }
    have transition : programStep resident zeroed = some final := by
      rw [fetched resident zeroed (entry + 4) _ (by simpa [Nat.add_assoc] using zeroPC) (by omega)
        (show resident[entry + 4]? = some (.branchZero 0 (word width zeroQuery)) by
          simpa [Nat.add_assoc] using jumpCode ⟨1, by simp⟩)]
      simp [step, zeroRunning, zeroValue, word, final]
    have jumpTrace : Execution resident zeroed final 1 zeroed.liveWords := by
      simpa only [show final.liveWords = zeroed.liveWords from rfl, Nat.zero_add, Nat.max_self] using
        Execution.cons transition (Execution.refl final)
    have readyLive : ready.liveWords = state.liveWords := by simp only [State.liveWords, readyHeap, readyStack, readyOutput]
    have zeroLive : zeroed.liveWords = state.liveWords := by
      simp only [State.liveWords, zeroHeap, zeroStack, zeroOutput]; exact readyLive
    have joined := healthyTrace.append (zeroTrace.append jumpTrace)
    rw [readyLive, zeroLive, Nat.max_self] at joined
    exact ⟨final, 5, by simpa using joined, by decide, zeroHeap.trans readyHeap,
      zeroStack.trans readyStack, zeroOutput.trans readyOutput, rfl, zeroRunning,
      (zeroFrame 4 (by decide)).trans ((readyFrame 4 (by decide)).trans candidateHeld),
      (zeroFrame 3 (by decide)).trans (readyFrame 3 (by decide)),
      fun register different => (zeroFrame register different).trans (readyFrame register different)⟩

end Controller.Cost.SharedRootClassify
