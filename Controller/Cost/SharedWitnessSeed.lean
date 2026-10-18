module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedHealthyReference

@[expose] public section

/-! Fetched constant/push instructions initialize root witness words on the stack. -/
namespace Controller.Cost.SharedWitnessSeed
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width : Nat) (sentinel : Word width) : Nat → List (Instruction width 8)
  | 0 => []
  | count + 1 => [.constant 3 sentinel, .push 3] ++ code width sentinel count

@[simp] theorem code_length (sentinel : Word width) (count : Nat) :
    (code width sentinel count).length = 2 * count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [code, ih]; omega

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (sentinel : Word width) (count entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 * count < 2 ^ width)
    (physical : SharedRootRead.BlockAt resident entry (code width sentinel count)) :
    ∃ final, Execution resident state final (2 * count) (state.liveWords + count) ∧
      final.heap = state.heap ∧ final.stack = List.replicate count sentinel ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 2 * count) ∧
      final.halted = false ∧ final.reg 4 = state.reg 4 := by
  induction count generalizing state entry with
  | zero =>
    refine ⟨state, ?_, rfl, by simp, rfl, by simpa using position, running, rfl⟩
    simpa using Execution.refl (p := resident) state
  | succ count ih =>
    let first := state.advance.put 3 sentinel
    let middle := { first.advance with stack := sentinel :: state.stack }
    have constantFetch : resident[entry]? = some (.constant 3 sentinel) := by
      simpa [code] using physical 0 (by simp [code])
    have pushFetch : resident[entry + 1]? = some (.push 3) := by
      simpa [code] using physical 1 (by simp [code])
    have constantStep : programStep resident state = some first := by
      rw [fetched resident state entry _ position (by omega) constantFetch]
      simp [step, running, first]
    have firstPC : first.pc = word width (entry + 1) := by
      simpa [first, State.put] using advance_position state position (by omega)
    have pushStep : programStep resident first = some middle := by
      rw [fetched resident first (entry + 1) _ firstPC (by omega) pushFetch]
      simp [step, first, middle, State.put, State.advance, running]
    have middlePC : middle.pc = word width (entry + 2) := by
      simpa [middle, Nat.add_assoc] using advance_position first firstPC (by omega)
    have firstLive : first.liveWords = state.liveWords := by
      simp [first, State.advance, State.put, State.liveWords]
    have middleLive : middle.liveWords = state.liveWords + 1 := by
      simp [middle, first, State.advance, State.put, State.liveWords]; omega
    have pairTrace : Execution resident state middle 2 (state.liveWords + 1) := by
      have trace := Execution.cons constantStep (Execution.cons pushStep (Execution.refl middle))
      simpa only [middleLive, firstLive, Nat.reduceAdd, Nat.max_eq_right (by omega : state.liveWords ≤ state.liveWords + 1)] using trace
    have restBlock : SharedRootRead.BlockAt resident (entry + 2) (code width sentinel count) := by
      intro offset valid
      have offsetBound : offset < 2 * count := by simpa using valid
      have fetchedRest := physical (2 + offset) (by simp [code]; omega)
      simpa [code, List.getElem_append_right, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using fetchedRest
    obtain ⟨final, restTrace, heap, stack, output, pc, active, reg⟩ :=
      ih middle (entry + 2) middlePC (by simpa [middle, first, State.advance, State.put] using running)
        (by omega) restBlock
    refine ⟨final, ?_, heap, ?_, output, ?_, active, ?_⟩
    · have joined := pairTrace.append restTrace
      rw [middleLive, Nat.max_eq_right (by omega : state.liveWords + 1 ≤ state.liveWords + 1 + count)] at joined
      simpa only [middleLive, Nat.mul_add, Nat.mul_one,
        Nat.max_eq_right (by omega : state.liveWords + 1 ≤ state.liveWords + 1 + count),
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined
    · rw [stack]
      change List.replicate count sentinel ++ sentinel :: state.stack = List.replicate (count + 1) sentinel ++ state.stack
      rw [List.replicate_succ', List.append_assoc]
      rfl
    · simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pc
    · simpa [middle, first, State.advance, State.put] using reg

end Controller.Cost.SharedWitnessSeed
