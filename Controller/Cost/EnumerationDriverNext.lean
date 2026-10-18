module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverStartup

@[expose] public section

/-! One concrete iterator call includes initial search and final exhaustion.
Its pointwise working-space bound excludes output history at every state. -/
namespace Controller.Cost.EnumerationDriverNext
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery
open Controller.Cost.EnumerationStreamEmit Controller.Cost.EnumerationWorkingTrace

/-- Uniform search charge for startup, successors and final exhaustion. -/
def delay (parameters : Parameters) (graph : DAG parameters.channels) : Nat :=
  (2 * parameters.channels + 1) * (budget parameters graph + 100)

/-- Pointwise working-word bound, excluding fixed code and external output. -/
def space (graph : DAG n) : Nat := 258 * (graph.countedSize + 1)

/-- Machine representation of the initial, after-result and exhausted iterator states. -/
def Runtime (parameters : Parameters) (graph : DAG parameters.channels) (packet : Array (Word width))
    (start seek : Nat) : Enumeration.State parameters.channels → State width 8 → Prop
  | .initial, state => state.heap = packet ∧ state.stack = [] ∧ state.halted = false ∧ state.pc = word width start
  | .after previous, state => Ready parameters packet parameters.channels parameters.channels previous state ∧
      state.pc = word width seek ∧ Detecting graph parameters.buses parameters.bridge.target parameters.drive previous
  | .exhausted, state => state.halted = true ∧ workingWords state ≤ space graph

private theorem start_delay (n Q : Nat) : n * (Q + 36) + Q + 4 * n + 18 ≤ (2 * n + 1) * (Q + 100) := by ring_nf; omega
private theorem seek_delay (n Q : Nat) : (n + n) * (Q + 60) + 4 ≤ (2 * n + 1) * (Q + 100) := by ring_nf; omega

private theorem scratch_space (G initial peak : Nat) (base : initial ≤ 6 * G + 14)
    (bound : peak ≤ initial + 244 * (G + 1)) : peak ≤ 258 * (G + 1) := by omega

theorem initial_drive_false (graph : DAG n) (b : Nat) (target : Fin n) :
    (next graph b target false .initial).output = none := by simp [next, query]

section
variable (parameters : Parameters) (graph : DAG parameters.channels)
  (retained entry : Nat) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
  (program : Program (EnumerationPrefixOracle.Width parameters graph retained) 8)
  (context : Context parameters graph retained entry rows roots program)
local notation "w" => EnumerationPrefixOracle.Width parameters graph retained
local notation "l" => EnumerationDriverCode.labels parameters graph w entry
local notation "packet" => EnumerationPrefixOracle.packet parameters w rows roots
include context

theorem initial_words (state : State w 8) (heap : state.heap = packet) (stack : state.stack = []) :
    workingWords state + 2 * parameters.channels ≤ 6 * graph.countedSize + 14 := by
  have packetSize : (packet).size = SharedDetectorPrepared.packetSize graph :=
    SharedDetectorPrepared.packet_size graph rows roots context.matched context.rootMatches (assignmentOfSet {parameters.bridge.target})
  have size := graph.countedSize_eq
  simp only [workingWords, heap, stack, List.length_nil, Nat.add_zero, packetSize,
    SharedDetectorPrepared.packetSize, SharedDetectorPrepared.maskBase, SharedDetectorPrepared.rootBase]
  omega

theorem runtime_words (logical : Enumeration.State parameters.channels) (state : State w 8)
    (runtime : Runtime parameters graph packet entry (l).seek logical state) : workingWords state ≤ space graph := by
  cases logical with
  | initial =>
    have bound := initial_words parameters graph retained entry rows roots program context state runtime.1 runtime.2.1
    dsimp [space]; omega
  | after previous =>
    have bound := EnumerationDriverWorking.ready_working_bound parameters graph retained entry rows roots program context
      parameters.channels parameters.channels previous state runtime.1
    dsimp [space]; omega
  | exhausted => exact runtime.2

set_option maxHeartbeats 2000000 in
theorem execution (logical : Enumeration.State parameters.channels) (state : State w 8)
    (runtime : Runtime parameters graph packet entry (l).seek logical state) :
    ∃ final ticks peak, WorkingExecution program state final ticks peak ∧ ticks ≤ delay parameters graph ∧
      peak ≤ space graph ∧ final.output = state.output ∧
      EnumerationDriverStart.Endpoint parameters packet (l).emit
        (next graph parameters.buses parameters.bridge.target parameters.drive logical).output final := by
  cases logical with
  | exhausted =>
    exact ⟨state, 0, workingWords state, WorkingExecution.refl state, by omega, runtime.2, rfl, runtime.1⟩
  | after previous =>
    have drive : parameters.drive = true := runtime.2.2.1
    have seekReady : Ready parameters packet parameters.channels parameters.channels (fixedTrue parameters.channels previous) state := by
      simpa only [EnumerationMasks.fixedTrue_full] using runtime.1
    obtain ⟨final, ticks, livePeak, trace, time, liveSpace, output, endpoint⟩ :=
      EnumerationDriverSeek.execution parameters graph retained entry rows roots program context previous runtime.2.2.2.1.2 parameters.channels
        state (by omega) seekReady runtime.2.1
    obtain ⟨peak, working, bound⟩ := quiet_bound trace output liveSpace
    have initial := EnumerationDriverWorking.ready_working_bound parameters graph retained entry rows roots program context
      parameters.channels parameters.channels previous state runtime.1
    refine ⟨final, ticks, peak, working, time.trans (seek_delay _ _), ?_, output, ?_⟩
    · exact scratch_space graph.countedSize (workingWords state) peak initial bound
    · simpa only [next, drive] using EnumerationDriverStart.endpoint_of_seek parameters packet (l).emit _ final endpoint
  | initial =>
    rcases runtime with ⟨heap, stack, running, position⟩
    have initial := initial_words parameters graph retained entry rows roots program context state heap stack
    cases drive : parameters.drive with
    | true =>
      obtain ⟨final, ticks, livePeak, trace, time, liveSpace, output, endpoint⟩ :=
        EnumerationDriverStartup.execution parameters graph retained entry rows roots program context drive state heap stack running position
      obtain ⟨peak, working, bound⟩ := quiet_bound (extra := 2 * parameters.channels + scratch parameters graph) trace output
        (by simpa only [Nat.add_assoc] using liveSpace)
      refine ⟨final, ticks, peak, working, time.trans (start_delay _ _), ?_, output, ?_⟩
      · exact scratch_space graph.countedSize (workingWords state + 2 * parameters.channels) peak initial
          (by simpa only [Nat.add_assoc] using bound)
      · simpa only [drive] using endpoint
    | false =>
      have initialAt := EnumerationDriverControlAt.initial parameters graph w entry rows roots program context.present
      rw [drive] at initialAt
      have initialRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 0 (by decide)
      simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_zero,
        List.length_append, List.length_cons, List.length_nil, EnumerationDriverCode.allocateWords_length,
        EnumerationDriverCode.jump] at initialRoom
      have startEq : (l).start = entry := rfl
      rw [startEq] at initialRoom
      have haltAt := EnumerationDriverLayout.physical parameters graph w entry rows roots program context.present 15 (by decide)
      change SharedRootRead.BlockAt program (l).halt [.halt] at haltAt
      have haltRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 15 (by decide)
      change (l).halt + 1 < 2 ^ w at haltRoom
      obtain ⟨final, trace, halted, finalHeap, finalStack, output⟩ :=
        EnumerationDriverInitial.drive_false program state entry (l).call (l).halt (EnumerationDriverCode.initWords parameters w)
          position running (by omega) haltRoom initialAt (by simpa using haltAt 0 (by simp))
      obtain ⟨peak, working, bound⟩ := quiet_bound (extra := 0) trace output (by omega)
      refine ⟨final, 3, peak, working, ?_, ?_, output, ?_⟩
      · dsimp [delay]; ring_nf; omega
      · change peak ≤ 258 * (graph.countedSize + 1); omega
      · rw [initial_drive_false]; exact halted

end
end Controller.Cost.EnumerationDriverNext
