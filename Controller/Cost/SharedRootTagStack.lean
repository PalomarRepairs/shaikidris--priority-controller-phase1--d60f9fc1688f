module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootInspect
public import Controller.Cost.SharedRegisterStack

@[expose] public section

namespace Controller.Cost.SharedRootTagStack
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def exposeCode (width : Nat) : Program width 8 := #[.pop 5, .pop 6]
def resumeCode (width : Nat) : Program width 8 := #[.push 6, .push 5]

@[simp] theorem exposeCode_size : (exposeCode width).size = 2 := rfl
@[simp] theorem resumeCode_size : (resumeCode width).size = 2 := rfl

set_option maxHeartbeats 2000000 in
theorem expose_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (cursor count : Word width) (suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (input : state.stack = cursor :: count :: suffix)
    (physical : CodeAt program entry (exposeCode width)) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.heap = state.heap ∧ final.output = state.output ∧ final.stack = suffix ∧
      final.reg 5 = cursor ∧ final.reg 6 = count ∧
      (∀ register : Fin 8, register ≠ 5 → register ≠ 6 → final.reg register = state.reg register) ∧
      final.pc = word width (entry + 2) ∧ final.halted = false := by
  let saved := fun register : Fin 8 => if register = 5 then cursor else count
  have block : SharedRootRead.BlockAt program entry (SharedRegisterStack.restoreCode [5, 6]) := by
    intro offset below
    have found := physical ⟨offset, by simpa [SharedRegisterStack.restoreCode] using below⟩
    have bound : offset < 2 := by simpa [SharedRegisterStack.restoreCode] using below
    interval_cases offset <;> simpa [exposeCode, SharedRegisterStack.restoreCode] using found
  obtain ⟨final, trace, heap, output, stack, frame, pc, active⟩ :=
    SharedRegisterStack.restore_execution program state entry [5, 6] saved suffix position running
      (by simpa using room) (by simpa [saved] using input) block
  refine ⟨final, by simpa using trace, heap, output, stack, ?_, ?_, ?_, by simpa using pc, active⟩
  · simpa [saved] using frame 5
  · simpa [saved] using frame 6
  · intro register notFive notSix
    simpa [notFive, notSix] using frame register

theorem resume_execution (program : Program width 8) (state : State width 8)
    (entry : Nat) (cursor count : Word width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (cursorHeld : state.reg 5 = cursor) (countHeld : state.reg 6 = count)
    (physical : CodeAt program entry (resumeCode width)) :
    ∃ final, Execution program state final 2 (state.liveWords + 2) ∧
      final.heap = state.heap ∧ final.output = state.output ∧ final.reg = state.reg ∧
      final.stack = cursor :: count :: state.stack ∧
      final.pc = word width (entry + 2) ∧ final.halted = false := by
  have block : SharedRootRead.BlockAt program entry (SharedRegisterStack.saveCode [6, 5]) := by
    intro offset below
    have found := physical ⟨offset, by simpa [SharedRegisterStack.saveCode] using below⟩
    have bound : offset < 2 := by simpa [SharedRegisterStack.saveCode] using below
    interval_cases offset <;> simpa [resumeCode, SharedRegisterStack.saveCode] using found
  obtain ⟨final, trace, heap, output, registers, stack, pc, active⟩ :=
    SharedRegisterStack.save_execution program state entry [6, 5] position running (by simpa using room) block
  exact ⟨final, by simpa using trace, heap, output, registers,
    by simpa [cursorHeld, countHeld] using stack, by simpa using pc, active⟩


def inspectCode (width n entry zeroQuery nextRoot : Nat) : Program width 8 :=
  exposeCode width ++ SharedRootInspect.code width n (entry + 2) zeroQuery nextRoot

@[simp] theorem inspectCode_size : (inspectCode width n entry zeroQuery nextRoot).size = 12 := by
  simp [inspectCode]

set_option maxHeartbeats 2000000 in
theorem inspect_execution (program : Program width 8) (state : State width 8)
    (n entry zeroQuery nextRoot address : Nat) (target : Fin n) (healthy : Bool)
    (candidate cursor count : Word width) (suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 12 < 2 ^ width) (capacity : n + 1 < 2 ^ width)
    (addressFits : address < 2 ^ width) (valid : address < state.heap.size)
    (addressHeld : state.reg 3 = word width address) (stored : state.heap[address]? = some candidate)
    (input : state.stack = cursor :: count ::
      (if healthy then word width target.val else word width (n + 1)) :: suffix)
    (physical : CodeAt program entry (inspectCode width n entry zeroQuery nextRoot)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 10 ∧
      final.heap = state.heap ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (if healthy then zeroQuery else
        if candidate = word width (n + 1) then nextRoot else entry + 12) ∧
      final.halted = false ∧ final.reg 5 = cursor ∧ final.reg 6 = count ∧
      final.reg 3 = state.reg 3 ∧ final.reg 4 = candidate := by
  have all := physical
  unfold inspectCode at all
  have exposeAt := RawSharedOrdered.takePrefix program entry _ _ all
  have inspectAt := RawSharedOrdered.takeSuffix program entry _ _ all
  obtain ⟨exposed, exposeTrace, exposeHeap, exposeOutput, exposeStack, cursorHeld, countHeld,
    exposeFrame, exposePC, exposeRunning⟩ :=
    expose_execution program state entry cursor count _ position running (by omega) input exposeAt
  obtain ⟨final, ticks, inspectTrace, time, heap, stack, output, pc, active, candidateHeld,
    addressFinal, frame⟩ :=
    SharedRootInspect.execution program exposed n (entry + 2) zeroQuery nextRoot address target healthy candidate
      suffix exposePC exposeRunning (by omega) capacity addressFits (by rw [exposeHeap]; exact valid)
      ((exposeFrame 3 (by decide) (by decide)).trans addressHeld) (by rw [exposeHeap]; exact stored)
      exposeStack (by simpa only [exposeCode_size] using inspectAt)
  have live : exposed.liveWords + 2 = state.liveWords := by
    simp only [State.liveWords, exposeHeap, exposeOutput, exposeStack, input, List.length_cons]
    omega
  refine ⟨final, 2 + ticks, ?_, by omega, heap.trans exposeHeap, stack, output.trans exposeOutput,
    ?_, active, (frame 5 (by decide) (by decide) (by decide)).trans cursorHeld,
    (frame 6 (by decide) (by decide) (by decide)).trans countHeld,
    addressFinal.trans (exposeFrame 3 (by decide) (by decide)), candidateHeld⟩
  · simpa only [Nat.max_eq_left (by omega : exposed.liveWords ≤ state.liveWords)] using
      exposeTrace.append inspectTrace
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using pc

end Controller.Cost.SharedRootTagStack
