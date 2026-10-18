module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedBaselineNonempty

@[expose] public section

/-! The retained baseline is evaluated only when its channel set is nonempty. -/
namespace Controller.Cost.SharedBaselineProbe
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops Controller.Cost.ForestInputStored

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) : Program width 8 :=
  SharedBaselineNonempty.code width (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size
    entry (entry + 5 * n + 3) (List.finRange n) ++
    (#[.branchZero 1 (word width done)] ++
      SharedReusableProbe.code width n rows roots (entry + 5 * n + 4) done)

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (code width n rows roots entry done).size = 5 * n + 171 := by unfold code; simp

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (witnesses suffix : List (Word width)) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry done))
    (room : entry + 5 * n + 171 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values)
    (input : state.stack = witnesses ++ suffix) (lengths : witnesses.length = graph.roots.length)
    (held : state.reg 4 = word width n) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 77 * graph.countedSize + 26 ∧
      peak ≤ 8 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = state.heap ∧
      final.stack = (if (List.finRange n).any values then
        SharedRootAggregate.updated (word width n)
          (graph.roots.map (fun root => (root.val, graph.eval values root))) witnesses else witnesses) ++ suffix ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = word width n := by
  have all := physical
  unfold code at all
  have scanCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailCode := RawSharedOrdered.takeSuffix resident entry _ _ all
  have restCode : CodeAt resident (entry + 5 * n + 3)
      (#[.branchZero 1 (word width done)] ++
        SharedReusableProbe.code width n rows roots (entry + 5 * n + 4) done) := by
    simpa [Nat.add_assoc] using tailCode
  have branchCode := RawSharedOrdered.takePrefix resident (entry + 5 * n + 3) _ _ restCode
  have probeCode := RawSharedOrdered.takeSuffix resident (entry + 5 * n + 3) _ _ restCode
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  obtain ⟨scanned, scanTicks, scanTrace, scanTime, scanValue, scanHeap, scanStack, scanOutput,
    scanPC, scanRunning, scanHead⟩ :=
    SharedBaselineNonempty.execution resident state
      (cacheHeap width (packetHeaderHeap width n rows roots) rows roots) values (List.finRange n)
      entry (entry + 5 * n + 3) position running (by simpa using (show entry + 5 * n + 3 < 2 ^ width from by omega))
      (by simp only [cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount]; omega)
      (by omega) heapStored scanCode
  have scanLive : scanned.liveWords = state.liveWords := by simp only [State.liveWords, scanHeap, scanStack, scanOutput]
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches values heapStored
  cases nonempty : (List.finRange n).any values with
  | false =>
    let final := { scanned.advance with pc := word width done }
    have transition : programStep resident scanned = some final := by
      rw [fetched resident scanned (entry + 5 * n + 3) _ scanPC (by omega)
        (show resident[entry + 5 * n + 3]? = some (.branchZero 1 (word width done)) by
          simpa using branchCode ⟨0, by simp⟩)]
      simp [step, scanRunning, scanValue, nonempty, boolWord, word, final]
    have branchTrace : Execution resident scanned final 1 scanned.liveWords := by
      simpa only [show final.liveWords = scanned.liveWords from rfl, Nat.zero_add, Nat.max_self] using
        Execution.cons transition (Execution.refl final)
    have joined := scanTrace.append branchTrace
    rw [scanLive, Nat.max_self] at joined
    refine ⟨final, scanTicks + 1, state.liveWords, joined, ?_, by omega, scanHeap,
      ?_, scanOutput, rfl, scanRunning, scanHead.trans held⟩
    · simp only [List.length_finRange] at scanTime; omega
    · simpa [nonempty, final, State.advance] using scanStack.trans input
  | true =>
    let ready := scanned.advance
    have transition : programStep resident scanned = some ready := by
      rw [fetched resident scanned (entry + 5 * n + 3) _ scanPC (by omega)
        (show resident[entry + 5 * n + 3]? = some (.branchZero 1 (word width done)) by
          simpa using branchCode ⟨0, by simp⟩)]
      simp [step, scanRunning, scanValue, nonempty, boolWord, word,
        Nat.mod_eq_of_lt (by omega : 1 < 2 ^ width), ready]
    have readyPC : ready.pc = word width (entry + 5 * n + 4) := by
      simpa [ready, Nat.add_assoc] using advance_position scanned scanPC (by omega)
    have branchTrace : Execution resident scanned ready 1 scanned.liveWords := by
      simpa only [show ready.liveWords = scanned.liveWords from rfl, Nat.zero_add, Nat.max_self] using
        Execution.cons transition (Execution.refl ready)
    obtain ⟨final, probeTicks, probePeak, probeTrace, probeTime, probeSpace, finalHeap,
      finalStack, finalOutput, finalPC, finalRunning, finalHead⟩ :=
      SharedReusableProbe.execution resident ready graph rows roots matched heads rootMatches values witnesses suffix
        (word width n) (entry + 5 * n + 4) done capacity (by simpa [Nat.add_assoc] using probeCode)
        (by omega) readyPC scanRunning (scanHeap.trans heapStored) (scanStack.trans input) lengths (scanHead.trans held)
    have joined := scanTrace.append (branchTrace.append probeTrace)
    rw [scanLive] at joined
    refine ⟨final, scanTicks + (1 + probeTicks), max state.liveWords (max state.liveWords probePeak),
      joined, ?_, ?_, finalHeap.trans scanHeap, by simpa only [nonempty, ite_true] using finalStack,
      finalOutput.trans scanOutput, finalPC, finalRunning, finalHead⟩
    · simp only [List.length_finRange] at scanTime; omega
    · simp only [ready, State.advance, scanStack, scanOutput] at probeSpace
      apply Nat.max_le.mpr
      constructor
      · omega
      · apply Nat.max_le.mpr
        constructor <;> omega

end Controller.Cost.SharedBaselineProbe
