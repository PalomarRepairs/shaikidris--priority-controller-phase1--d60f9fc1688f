module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverCapacity

@[expose] public section

/-! Actual initial-answer continuation: an infeasible initial prefix halts,
while a feasible one enters the fixed completion block at depth zero. -/
namespace Controller.Cost.EnumerationDriverStart
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.SharedDetectorAssembly
open Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery

/-- A search result is either an actual halt or a full prefix ready to emit. -/
def Endpoint (parameters : Parameters) (packet : Array (Word width)) (emit : Nat)
    (result : Option (Finset (Fin parameters.channels))) (state : State width 8) : Prop :=
  match result with
  | none => state.halted = true
  | some K => Ready parameters packet parameters.channels parameters.channels K state ∧ state.pc = word width emit

theorem endpoint_of_seek (parameters : Parameters) (packet : Array (Word width)) (emit : Nat)
    (result : Option (Finset (Fin parameters.channels))) (state : State width 8)
    (endpoint : EnumerationDriverSeek.Endpoint parameters packet emit result state) : Endpoint parameters packet emit result state := by
  cases result with
  | none => exact endpoint.1
  | some K => exact endpoint

section
variable (parameters : Parameters) (graph : DAG parameters.channels)
  (retained entry : Nat) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
  (program : Program (EnumerationPrefixOracle.Width parameters graph retained) 8)
  (context : Context parameters graph retained entry rows roots program)
local notation "w" => EnumerationPrefixOracle.Width parameters graph retained
local notation "l" => EnumerationDriverCode.labels parameters graph w entry
local notation "packet" => EnumerationPrefixOracle.packet parameters w rows roots
include context

set_option maxHeartbeats 2000000 in
theorem answer_entry (answer : Bool) (state : State w 8)
    (ready : Ready parameters packet 0 0 ∅ state) (position : state.pc = word w (l).initialPost)
    (flag : state.reg 4 = boolWord w answer) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 3 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      (if answer then Ready parameters packet 0 0 ∅ final ∧ final.pc = word w (l).descend else final.halted = true) := by
  have postAt := EnumerationDriverLayout.physical parameters graph w entry rows roots program context.present 6 (by decide)
  change SharedRootRead.BlockAt program (l).initialPost ([.branchZero 4 (word w (l).halt)] ++ EnumerationDriverCode.jump w (l).descend) at postAt
  have branchAt : program[(l).initialPost]? = some (.branchZero 4 (word w (l).halt)) := by simpa using postAt 0 (by simp [EnumerationDriverCode.jump])
  have jumpAt := block_right program (l).initialPost [.branchZero 4 (word w (l).halt)] (EnumerationDriverCode.jump w (l).descend) postAt
  have room := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 6 (by decide)
  change (l).initialPost + 3 < 2 ^ w at room
  have fits : 1 < 2 ^ w := by omega
  cases answer with
  | false =>
    obtain ⟨branched, first, pc, heap, stack, output, running, frame⟩ :=
      EnumerationSteps.branch_taken (program := program) state (l).initialPost (l).halt 4 position ready.running (by omega)
        (by rw [flag, boolWord_val w fits]; rfl) branchAt
    have haltAt := EnumerationDriverLayout.physical parameters graph w entry rows roots program context.present 15 (by decide)
    change SharedRootRead.BlockAt program (l).halt [.halt] at haltAt
    have haltRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 15 (by decide)
    change (l).halt + 1 < 2 ^ w at haltRoom
    obtain ⟨final, second, halted, finalHeap, finalStack, finalOutput⟩ :=
      EnumerationSteps.halt_execution (program := program) branched (l).halt pc running haltRoom (by simpa using haltAt 0 (by simp))
    have branchLive : branched.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
    exact ⟨final, 2, by simpa only [branchLive, Nat.max_self, Nat.reduceAdd] using first.append second,
      by omega, finalHeap.trans heap, finalStack.trans stack, finalOutput.trans output, halted⟩
  | true =>
    obtain ⟨branched, first, pc, heap, stack, output, running, frame⟩ :=
      EnumerationSteps.branch_skipped (program := program) state (l).initialPost (l).halt 4 position ready.running (by omega)
        (by rw [flag, boolWord_val w fits]; decide) branchAt
    obtain ⟨final, second, finalPC, finalHeap, finalStack, finalOutput, finalRunning, finalFrame⟩ :=
      EnumerationSteps.jump_execution (program := program) branched ((l).initialPost + 1) (l).descend pc running (by omega)
        (by simpa [EnumerationDriverCode.jump] using jumpAt 0 (by simp [EnumerationDriverCode.jump]))
        (by simpa [EnumerationDriverCode.jump] using jumpAt 1 (by simp [EnumerationDriverCode.jump]))
    have branchLive : branched.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
    exact ⟨final, 3, by simpa only [branchLive, Nat.max_self, Nat.reduceAdd] using first.append second,
      by omega, finalHeap.trans heap, finalStack.trans stack, finalOutput.trans output,
      ⟨⟨finalHeap.trans (heap.trans ready.heap), (finalFrame 3 (by decide)).trans ((frame 3).trans ready.counter),
        finalStack.trans (stack.trans ready.stack), finalRunning⟩, finalPC⟩⟩

end
end Controller.Cost.EnumerationDriverStart
