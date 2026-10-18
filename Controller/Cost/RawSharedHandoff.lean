module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.RawTypedCopy
public import Controller.Cost.UniformDAGRuntimeOutputs

@[expose] public section

/-! The raw caller's fetched handoff enters the shared DAG evaluator in the
same eight-register machine. The source packet and assignment remain on the
actual stack; high registers are framed throughout the relocated execution. -/
namespace Controller.Cost.RawSharedHandoff
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.RegisterWiden Controller.Cost.RawAdapterProgram

set_option maxHeartbeats 2000000 in
/-- The handoff clears register three and jumps into the resident shared
interpreter. All roots are emitted from the runtime packet and the machine halts. -/
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (suffix : List (Word width)) (entry typedEntry : ℕ)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : ∀ index (valid : index <
        (widenProgram (UniformDAGRuntimeOutputs.program width n rows roots values)).size),
      resident[typedEntry + index]? = some (relocatedInstruction typedEntry
        ((widenProgram (UniformDAGRuntimeOutputs.program width n rows roots values))[index]'valid)))
    (codeFits : typedEntry +
      (widenProgram (UniformDAGRuntimeOutputs.program width n rows roots values)).size < 2 ^ width)
    (handoffPhysical : ∀ phase : Fin 2, resident[entry + phase.val]? =
      (RawTypedCopy.typedColdHandoffCode width typedEntry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (handoffFits : entry + 2 < 2 ^ width) (zero : state.reg 6 = word width 0)
    (empty : state.heap = #[])
    (input : state.stack = (inputPacket n 0 rows roots).map (word width) ++
      List.ofFn (fun i => boolWord width (values i)) ++ suffix) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 97 * graph.countedSize + 39 ∧
      peak ≤ max state.liveWords
        (8 * graph.countedSize + 18 + suffix.length + state.output.length) ∧
      final.stack = suffix ∧
      final.output = ((graph.outputValues values).map (boolWord width)).reverse ++ state.output ∧
      final.halted = true := by
  obtain ⟨ready, handoff, readyEq⟩ := RawTypedCopy.typed_cold_handoff_execution resident
    entry typedEntry state handoffPhysical position running handoffFits zero empty
  obtain ⟨final, ticks, peak, trace, time, space, stack, output, halted⟩ :=
    UniformDAGRuntimeOutputs.execution_at_width graph rows roots matched heads rootMatches values
      width capacity suffix state.output (state.reg 0) (state.reg 1) (state.reg 2)
  have widened := widen_execution _ _ _ _ _ trace state.reg
  have relocated := relocated_execution resident _ typedEntry physical codeFits widened
  have startEq : relocatedState typedEntry
      (widenState
        ((ForestCounter.counterState (#[] : Array (Word width)) 0
          (state.reg 0) (state.reg 1) (state.reg 2)).frame
          ((inputPacket n 0 rows roots).map (word width) ++
            List.ofFn (fun i => boolWord width (values i)) ++ suffix) state.output)
        state.reg) = ready := by
    rw [readyEq, input]
    simp [relocatedState, widenState, SparseConeTraversal.widenState,
      ForestCounter.counterState, State.frame, word, List.append_assoc]
  rw [startEq] at relocated
  have joined := handoff.append relocated
  refine ⟨relocatedState typedEntry (widenState final state.reg), _, _, joined, ?_, ?_, stack, output, halted⟩
  · omega
  · apply max_le (le_max_left _ _)
    exact le_trans (by omega) (le_max_right _ _)

set_option maxHeartbeats 2000000 in
/-- Saving the produced packet and releasing the old heap precede the shared
evaluator in one trace. The time bound charges the packet once and has no
per-root cone-extraction term. -/
theorem transfer_execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (suffix : List (Word width))
    (nodes base origin recoverEntry saveSetupEntry saveEntry releaseSetupEntry releaseEntry
      handoffEntry typedEntry : ℕ)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : ∀ index (valid : index <
        (widenProgram (UniformDAGRuntimeOutputs.program width n rows roots values)).size),
      resident[typedEntry + index]? = some (relocatedInstruction typedEntry
        ((widenProgram (UniformDAGRuntimeOutputs.program width n rows roots values))[index]'valid)))
    (codeFits : typedEntry +
      (widenProgram (UniformDAGRuntimeOutputs.program width n rows roots values)).size < 2 ^ width)
    (recoverPhysical : ∀ phase : Fin 2, resident[recoverEntry + phase.val]? =
      (RawTypedCopy.typedOriginRecoverCode width nodes base)[phase.val]?)
    (setupPhysical : ∀ phase : Fin 8, resident[saveSetupEntry + phase.val]? =
      (RawTypedCopy.typedSaveSetupCode width
        ((inputPacket n 0 rows roots).map (word width)).length saveEntry)[phase.val]?)
    (savePhysical : RawTransferLoops.CodeAt resident saveEntry
      (RawTransferLoops.reverseSaveCode width saveEntry releaseSetupEntry))
    (releaseSetupPhysical : ∀ phase : Fin 2, resident[releaseSetupEntry + phase.val]? =
      (RawTypedCopy.typedReleaseSetupCode width releaseEntry)[phase.val]?)
    (releasePhysical : RawTransferLoops.CodeAt resident releaseEntry
      (RawTransferLoops.countedReleaseCode width releaseEntry handoffEntry))
    (handoffPhysical : ∀ phase : Fin 2, resident[handoffEntry + phase.val]? =
      (RawTypedCopy.typedColdHandoffCode width typedEntry)[phase.val]?)
    (recoverNext : recoverEntry + 2 = saveSetupEntry)
    (position : state.pc = word width recoverEntry) (running : state.halted = false)
    (recoverFits : recoverEntry + 2 < 2 ^ width) (setupFits : saveSetupEntry + 8 < 2 ^ width)
    (saveFits : saveEntry + 6 < 2 ^ width)
    (releaseSetupFits : releaseSetupEntry + 2 < 2 ^ width)
    (releaseFits : releaseEntry + 4 < 2 ^ width) (handoffFits : handoffEntry + 2 < 2 ^ width)
    (originPositive : 0 < origin) (packetPositive : 0 < (inputPacket n 0 rows roots).length)
    (room : origin + (inputPacket n 0 rows roots).length < 2 ^ width)
    (allocation : state.heap.size = origin + (inputPacket n 0 rows roots).length)
    (slotFits : Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base < 2 ^ width)
    (originCell : state.heap[Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base]? =
      some (word width origin))
    (cells : RawTypedCopy.CopiedPacketCells state.heap origin
      ((inputPacket n 0 rows roots).map (word width)))
    (input : state.stack = List.ofFn (fun i => boolWord width (values i)) ++ suffix) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 6 * (inputPacket n 0 rows roots).length + 4 * state.heap.size +
        97 * graph.countedSize + 53 ∧
      peak ≤ max (state.liveWords + (inputPacket n 0 rows roots).length)
        (8 * graph.countedSize + 18 + suffix.length + state.output.length) ∧
      final.stack = suffix ∧
      final.output = ((graph.outputValues values).map (boolWord width)).reverse ++ state.output ∧
      final.halted = true := by
  obtain ⟨released, transferPeak, transfer, transferBound, empty, savedStack,
      savedOutput, releasedPC, releasedRunning, releasedZero⟩ :=
    RawTypedCopy.typed_packet_save_release_execution resident nodes base origin recoverEntry
      saveSetupEntry saveEntry releaseSetupEntry releaseEntry handoffEntry
      ((inputPacket n 0 rows roots).map (word width)) state recoverPhysical setupPhysical
      savePhysical releaseSetupPhysical releasePhysical recoverNext position running recoverFits
      setupFits saveFits releaseSetupFits releaseFits originPositive (by simpa using packetPositive)
      (by simpa using room) (by simpa using allocation) slotFits originCell cells
  obtain ⟨final, ticks, peak, run, time, space, stack, output, halted⟩ :=
    execution resident released graph rows roots matched heads rootMatches values suffix
      handoffEntry typedEntry capacity physical codeFits handoffPhysical releasedPC releasedRunning
      handoffFits releasedZero empty (by simp [savedStack, input, List.append_assoc])
  have releasedLive := transfer.final_storage_le
  have joined := transfer.append run
  refine ⟨final, _, _, joined, ?_, ?_, stack, ?_, halted⟩
  · simp only [List.length_map]
    omega
  · simp only [List.length_map] at transferBound
    rw [savedOutput] at space
    apply max_le
    · exact le_trans transferBound (le_max_left _ _)
    · exact le_trans space (max_le_max (le_trans releasedLive transferBound) le_rfl)
  · simpa only [savedOutput] using output

end Controller.Cost.RawSharedHandoff
