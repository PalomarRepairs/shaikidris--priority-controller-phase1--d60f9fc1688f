module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.RawTypedCopyRows

public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Controller.Cost.RawTypedCopy
open Controller.Cost
variable {width : Nat}
open Controller.Cost
open Controller.Decoder Controller.Cost.ForestIndexedOperands
open Controller.Cost.SparseConeTraversal
open Controller.Decoder Controller.Cost.SparseConeTraversal
open Controller.Cost.SparseConeReuse

-- Fixed fetched handoff after counted release. Low registers0/1/2 may retain
-- arbitrary words because ForestCounter.counterState exposes those inputs;
-- low register3 is explicitly cleared by the actual code, not state reset.


theorem copied_packet_runtime_cold_execution (graph : DAG n)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat)
    (matched : ForestIndexedOperands.RowsMatch graph rows)
    (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : ForestIndexedOperands.RootsMatch graph roots)
    (assignment : Assignment n)
    (suffix : List (Word (typedExecutionWidth graph)))
    (resident : Program (typedExecutionWidth graph) 8)
    (nodes base origin recoverEntry saveSetupEntry saveEntry releaseSetupEntry releaseEntry handoffEntry typedEntry : Nat)
    (state : State (typedExecutionWidth graph) 8)
    (recoverPhysical : ∀ phase : Fin 2, resident[recoverEntry + phase.val]? =
      (typedOriginRecoverCode (typedExecutionWidth graph) nodes base)[phase.val]?)
    (setupPhysical : ∀ phase : Fin 24, resident[saveSetupEntry + phase.val]? =
      (typedRuntimeSaveSetupCode (typedExecutionWidth graph) saveEntry)[phase.val]?)
    (savePhysical : RawTransferLoops.CodeAt resident saveEntry
      (RawTransferLoops.reverseSaveCode (typedExecutionWidth graph) saveEntry releaseSetupEntry))
    (releaseSetupPhysical : ∀ phase : Fin 2, resident[releaseSetupEntry + phase.val]? =
      (typedReleaseSetupCode (typedExecutionWidth graph) releaseEntry)[phase.val]?)
    (releasePhysical : RawTransferLoops.CodeAt resident releaseEntry
      (RawTransferLoops.countedReleaseCode (typedExecutionWidth graph) releaseEntry handoffEntry))
    (handoffPhysical : ∀ phase : Fin 2, resident[handoffEntry + phase.val]? =
      (typedColdHandoffCode (typedExecutionWidth graph) typedEntry)[phase.val]?)
    (coldPhysical : ∀ index (valid : index <
      (typedShapeCode (typedExecutionWidth graph) n graph.nodeCount
        (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length).size),
      resident[typedEntry + index]? = some (RawAdapterProgram.relocatedInstruction typedEntry
        ((typedShapeCode (typedExecutionWidth graph) n graph.nodeCount
          (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length)[index]'valid)))
    (recoverNext : recoverEntry + 2 = saveSetupEntry)
    (position : state.pc = word (typedExecutionWidth graph) recoverEntry)
    (running : state.halted = false)
    (recoverFits : recoverEntry + 2 < 2 ^ typedExecutionWidth graph)
    (setupFits : saveSetupEntry + 24 < 2 ^ typedExecutionWidth graph)
    (saveFits : saveEntry + 6 < 2 ^ typedExecutionWidth graph)
    (releaseSetupFits : releaseSetupEntry + 2 < 2 ^ typedExecutionWidth graph)
    (releaseFits : releaseEntry + 4 < 2 ^ typedExecutionWidth graph)
    (handoffFits : handoffEntry + 2 < 2 ^ typedExecutionWidth graph)
    (coldFits : typedEntry +
      (typedShapeCode (typedExecutionWidth graph) n graph.nodeCount
        (ForestIndexedOperands.rowChildren rows).length (ForestIndexedOperands.rowGuards rows).length roots.length).size <
      2 ^ typedExecutionWidth graph)
    (originPositive : 0 < origin)
    (packetPositive : 0 < (typedPacketWords graph rows roots).length)
    (room : origin + (typedPacketWords graph rows roots).length < 2 ^ typedExecutionWidth graph)
    (allocation : state.heap.size = origin + (typedPacketWords graph rows roots).length)
    (slotFits : Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base < 2 ^ typedExecutionWidth graph)
    (originCell : state.heap[Controller.Horn.WorklistBucketReady.nextSlot (n := nodes) base]? =
      some (word (typedExecutionWidth graph) origin))
    (cells : CopiedPacketCells state.heap origin (typedPacketWords graph rows roots))
    (zeroHeld : state.reg 6 = word (typedExecutionWidth graph) 0)
    (maskHeld : state.reg 7 = word (typedExecutionWidth graph) (2 ^ typedExecutionWidth graph - 1))
    (inputStack : state.stack =
      List.ofFn (fun channel => boolWord (typedExecutionWidth graph) (assignment channel)) ++ suffix) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 6 * (typedPacketWords graph rows roots).length + 4 * state.heap.size +
        142 * graph.countedSize + 226 * (graph.roots.map (typedConeIncidenceSize graph)).sum + 76 ∧
      peak ≤ max (state.liveWords + (typedPacketWords graph rows roots).length)
        (38 * graph.countedSize + 1884 + suffix.length + state.output.length) ∧
      final.stack = suffix ∧
      final.output = (graph.roots.map (fun node => boolWord (typedExecutionWidth graph)
        (graph.eval assignment node))).reverse ++ state.output ∧ final.halted = true := by
  have image := ForestIndexedOperands.matched_cold_input_words
    (width := typedExecutionWidth graph) graph rows roots matched rootMatches
  have stored : CopiedPacketCells state.heap origin
      ([word (typedExecutionWidth graph) n, word (typedExecutionWidth graph) graph.nodeCount,
        word (typedExecutionWidth graph) graph.childIncidences, word (typedExecutionWidth graph) graph.guardIncidences,
        word (typedExecutionWidth graph) graph.roots.length] ++
        (serializedRows 5 rows roots).map (word (typedExecutionWidth graph))) := by
    simpa only [typedPacketWords, image] using cells
  have nodeCell : state.heap[origin + 1]? = some (word (typedExecutionWidth graph) graph.nodeCount) := by
    simpa using stored ⟨1, by simp⟩
  have childCell : state.heap[origin + 2]? = some (word (typedExecutionWidth graph) graph.childIncidences) := by
    simpa using stored ⟨2, by simp⟩
  have guardCell : state.heap[origin + 3]? = some (word (typedExecutionWidth graph) graph.guardIncidences) := by
    simpa using stored ⟨3, by simp⟩
  have rootCell : state.heap[origin + 4]? = some (word (typedExecutionWidth graph) graph.roots.length) := by
    simpa using stored ⟨4, by simp⟩
  obtain ⟨released, transferPeak, transfer, transferBound, empty, savedStack,
      savedOutput, releasedPC, releasedRunning, releasedZero⟩ :=
    typed_packet_runtime_save_release_execution resident nodes graph.nodeCount graph.childIncidences
      graph.guardIncidences graph.roots.length base origin recoverEntry saveSetupEntry saveEntry
      releaseSetupEntry releaseEntry handoffEntry (typedPacketWords graph rows roots) state
      recoverPhysical setupPhysical savePhysical releaseSetupPhysical releasePhysical recoverNext
      position running recoverFits setupFits saveFits releaseSetupFits releaseFits originPositive
      packetPositive room allocation slotFits originCell
      (typed_input_length graph rows roots matched rootMatches) zeroHeld maskHeld
      nodeCell childCell guardCell rootCell cells
  obtain ⟨ready, handoff, readyEq⟩ :=
    typed_cold_handoff_execution resident handoffEntry typedEntry released handoffPhysical
      releasedPC releasedRunning handoffFits releasedZero empty
  have readyStart : ready = RawAdapterProgram.relocatedState typedEntry (widenState
      ((ForestCounter.counterState (#[] : Array (Word (typedExecutionWidth graph))) 0
        (released.reg 0) (released.reg 1) (released.reg 2)).frame
        ((typedPacketWords graph rows roots) ++
          List.ofFn (fun channel => boolWord (typedExecutionWidth graph) (assignment channel)) ++ suffix)
        state.output) released.reg) := by
    rw [readyEq, savedStack, inputStack, savedOutput]
    simp only [List.append_assoc, RawAdapterProgram.relocatedState,
      widenState, ForestCounter.counterState, Controller.Cost.State.frame, word,
      Nat.zero_mod, Nat.zero_add]
  obtain ⟨final, coldTicks, coldPeak, cold, coldTime, coldSpace, finalStack, finalOutput, finalHalted⟩ :=
    typed_shape_resident_execution graph rows roots matched heads rootMatches assignment suffix state.output
      (released.reg 0) (released.reg 1) (released.reg 2) released.reg resident typedEntry coldPhysical coldFits
  have coldFromReady : Execution resident ready final coldTicks coldPeak := by
    rw [readyStart]
    exact cold
  have releasedLive : released.liveWords ≤ transferPeak := Execution.final_storage_le transfer
  have readyLive : ready.liveWords ≤ released.liveWords := Execution.final_storage_le handoff
  have coldBound : coldPeak ≤ 38 * graph.countedSize + 1884 + suffix.length + state.output.length := by
    omega
  have joined := (transfer.append handoff).append coldFromReady
  refine ⟨final, _, _, joined, ?_, ?_, finalStack, finalOutput, finalHalted⟩
  · omega
  · simp only [max_le_iff]
    constructor
    · constructor
      · exact le_trans transferBound (le_max_left _ _)
      · exact le_trans (le_trans releasedLive transferBound) (le_max_left _ _)
    · exact le_trans coldBound (le_max_right _ _)


/-- Copy and transfer code derives the saved payload length from its stored
header. The typed code suffix uses the counted original sizes and layout. -/
@[irreducible] def typedCopyColdCode (width channels nodes children guards roots base entry : Nat) : Program width 8 :=
  orderedTypedCopyCode width nodes children base entry (entry + 207) ++
  typedOriginRecoverCode width nodes base ++
  typedRuntimeSaveSetupCode width (entry + 233) ++
  RawTransferLoops.reverseSaveCode width (entry + 233) (entry + 239) ++
  typedReleaseSetupCode width (entry + 241) ++
  RawTransferLoops.countedReleaseCode width (entry + 241) (entry + 245) ++
  typedColdHandoffCode width (entry + 247) ++
  (typedShapeCode width channels nodes children guards roots).map
    (RawAdapterProgram.relocatedInstruction (entry + 247))

private theorem typedRuntimeSaveSetupCode_size (width saveEntry : Nat) :
    (typedRuntimeSaveSetupCode width saveEntry).size = 24 := rfl

theorem typedOriginRecoverCode_size (width nodes base : Nat) :
    (typedOriginRecoverCode width nodes base).size = 2 := rfl

theorem typedReleaseSetupCode_size (width entry : Nat) :
    (typedReleaseSetupCode width entry).size = 2 := rfl

theorem typedColdHandoffCode_size (width entry : Nat) :
    (typedColdHandoffCode width entry).size = 2 := rfl

private theorem typedCopyColdCode_size (width channels nodes children guards roots base entry : Nat) :
    (typedCopyColdCode width channels nodes children guards roots base entry).size =
      247 + (typedShapeCode width channels nodes children guards roots).size := by
  unfold typedCopyColdCode
  simp only [Array.size_append, Array.size_map, orderedTypedCopyCode_size,
    typedOriginRecoverCode_size, typedRuntimeSaveSetupCode_size,
    RawTransferLoops.reverseSaveCode_size, typedReleaseSetupCode_size,
    RawTransferLoops.countedReleaseCode_size, typedColdHandoffCode_size]

private theorem typed_caller_copy_part (resident : Program width 8)
    (channels nodes children guards roots base entry : Nat)
    (physical : ∀ phase : Fin (typedCopyColdCode width channels nodes children guards roots base entry).size,
      resident[entry + phase.val]? =
        (typedCopyColdCode width channels nodes children guards roots base entry)[phase.val]?) :
    ∀ phase : Fin 207, resident[(entry + 0) + phase.val]? =
      (orderedTypedCopyCode width nodes children base entry (entry + 207))[phase.val]? := by
  let whole := typedCopyColdCode width channels nodes children guards roots base entry
  let before : Program width 8 := #[]
  let fragment := orderedTypedCopyCode width nodes children base entry (entry + 207)
  let after : Program width 8 := typedOriginRecoverCode width nodes base ++ typedRuntimeSaveSetupCode width (entry + 233) ++ RawTransferLoops.reverseSaveCode width (entry + 233) (entry + 239) ++ typedReleaseSetupCode width (entry + 241) ++ RawTransferLoops.countedReleaseCode width (entry + 241) (entry + 245) ++ typedColdHandoffCode width (entry + 247) ++ (typedShapeCode width channels nodes children guards roots).map (RawAdapterProgram.relocatedInstruction (entry + 247))
  have layout : whole = (before ++ fragment) ++ after := by
    dsimp only [whole, before, fragment, after]
    unfold typedCopyColdCode
    simp only [Array.append_assoc, Array.empty_append]
  have beforeSize : before.size = 0 := by
    dsimp only [before]
    simp only [Array.size_append, Array.size_empty, orderedTypedCopyCode_size,
      typedOriginRecoverCode_size, typedRuntimeSaveSetupCode_size,
      RawTransferLoops.reverseSaveCode_size, typedReleaseSetupCode_size,
      RawTransferLoops.countedReleaseCode_size, typedColdHandoffCode_size]
  have fragmentSize : fragment.size = 207 := by
    dsimp only [fragment]
    simp only [orderedTypedCopyCode_size]
  exact extract_copy_section resident whole before fragment after entry 0 207
    layout beforeSize fragmentSize physical

private theorem typed_caller_recover_part (resident : Program width 8)
    (channels nodes children guards roots base entry : Nat)
    (physical : ∀ phase : Fin (typedCopyColdCode width channels nodes children guards roots base entry).size,
      resident[entry + phase.val]? =
        (typedCopyColdCode width channels nodes children guards roots base entry)[phase.val]?) :
    ∀ phase : Fin 2, resident[(entry + 207) + phase.val]? =
      (typedOriginRecoverCode width nodes base)[phase.val]? := by
  let whole := typedCopyColdCode width channels nodes children guards roots base entry
  let before : Program width 8 := orderedTypedCopyCode width nodes children base entry (entry + 207)
  let fragment := typedOriginRecoverCode width nodes base
  let after : Program width 8 := typedRuntimeSaveSetupCode width (entry + 233) ++ RawTransferLoops.reverseSaveCode width (entry + 233) (entry + 239) ++ typedReleaseSetupCode width (entry + 241) ++ RawTransferLoops.countedReleaseCode width (entry + 241) (entry + 245) ++ typedColdHandoffCode width (entry + 247) ++ (typedShapeCode width channels nodes children guards roots).map (RawAdapterProgram.relocatedInstruction (entry + 247))
  have layout : whole = (before ++ fragment) ++ after := by
    dsimp only [whole, before, fragment, after]
    unfold typedCopyColdCode
    simp only [Array.append_assoc, Array.empty_append]
  have beforeSize : before.size = 207 := by
    dsimp only [before]
    simp only [Array.size_append, Array.size_empty, orderedTypedCopyCode_size,
      typedOriginRecoverCode_size, typedRuntimeSaveSetupCode_size,
      RawTransferLoops.reverseSaveCode_size, typedReleaseSetupCode_size,
      RawTransferLoops.countedReleaseCode_size, typedColdHandoffCode_size]
  have fragmentSize : fragment.size = 2 := by
    dsimp only [fragment]
    simp only [typedOriginRecoverCode_size]
  exact extract_copy_section resident whole before fragment after entry 207 2
    layout beforeSize fragmentSize physical

private theorem typed_caller_runtime_part (resident : Program width 8)
    (channels nodes children guards roots base entry : Nat)
    (physical : ∀ phase : Fin (typedCopyColdCode width channels nodes children guards roots base entry).size,
      resident[entry + phase.val]? =
        (typedCopyColdCode width channels nodes children guards roots base entry)[phase.val]?) :
    ∀ phase : Fin 24, resident[(entry + 209) + phase.val]? =
      (typedRuntimeSaveSetupCode width (entry + 233))[phase.val]? := by
  let whole := typedCopyColdCode width channels nodes children guards roots base entry
  let before : Program width 8 := orderedTypedCopyCode width nodes children base entry (entry + 207) ++ typedOriginRecoverCode width nodes base
  let fragment := typedRuntimeSaveSetupCode width (entry + 233)
  let after : Program width 8 := RawTransferLoops.reverseSaveCode width (entry + 233) (entry + 239) ++ typedReleaseSetupCode width (entry + 241) ++ RawTransferLoops.countedReleaseCode width (entry + 241) (entry + 245) ++ typedColdHandoffCode width (entry + 247) ++ (typedShapeCode width channels nodes children guards roots).map (RawAdapterProgram.relocatedInstruction (entry + 247))
  have layout : whole = (before ++ fragment) ++ after := by
    dsimp only [whole, before, fragment, after]
    unfold typedCopyColdCode
    simp only [Array.append_assoc, Array.empty_append]
  have beforeSize : before.size = 209 := by
    dsimp only [before]
    simp only [Array.size_append, Array.size_empty, orderedTypedCopyCode_size,
      typedOriginRecoverCode_size, typedRuntimeSaveSetupCode_size,
      RawTransferLoops.reverseSaveCode_size, typedReleaseSetupCode_size,
      RawTransferLoops.countedReleaseCode_size, typedColdHandoffCode_size]
  have fragmentSize : fragment.size = 24 := by
    dsimp only [fragment]
    simp only [typedRuntimeSaveSetupCode_size]
  exact extract_copy_section resident whole before fragment after entry 209 24
    layout beforeSize fragmentSize physical

private theorem typed_caller_save_part (resident : Program width 8)
    (channels nodes children guards roots base entry : Nat)
    (physical : ∀ phase : Fin (typedCopyColdCode width channels nodes children guards roots base entry).size,
      resident[entry + phase.val]? =
        (typedCopyColdCode width channels nodes children guards roots base entry)[phase.val]?) :
    ∀ phase : Fin 6, resident[(entry + 233) + phase.val]? =
      (RawTransferLoops.reverseSaveCode width (entry + 233) (entry + 239))[phase.val]? := by
  let whole := typedCopyColdCode width channels nodes children guards roots base entry
  let before : Program width 8 := orderedTypedCopyCode width nodes children base entry (entry + 207) ++ typedOriginRecoverCode width nodes base ++ typedRuntimeSaveSetupCode width (entry + 233)
  let fragment := RawTransferLoops.reverseSaveCode width (entry + 233) (entry + 239)
  let after : Program width 8 := typedReleaseSetupCode width (entry + 241) ++ RawTransferLoops.countedReleaseCode width (entry + 241) (entry + 245) ++ typedColdHandoffCode width (entry + 247) ++ (typedShapeCode width channels nodes children guards roots).map (RawAdapterProgram.relocatedInstruction (entry + 247))
  have layout : whole = (before ++ fragment) ++ after := by
    dsimp only [whole, before, fragment, after]
    unfold typedCopyColdCode
    simp only [Array.append_assoc, Array.empty_append]
  have beforeSize : before.size = 233 := by
    dsimp only [before]
    simp only [Array.size_append, Array.size_empty, orderedTypedCopyCode_size,
      typedOriginRecoverCode_size, typedRuntimeSaveSetupCode_size,
      RawTransferLoops.reverseSaveCode_size, typedReleaseSetupCode_size,
      RawTransferLoops.countedReleaseCode_size, typedColdHandoffCode_size]
  have fragmentSize : fragment.size = 6 := by
    dsimp only [fragment]
    simp only [RawTransferLoops.reverseSaveCode_size]
  exact extract_copy_section resident whole before fragment after entry 233 6
    layout beforeSize fragmentSize physical

private theorem typed_caller_releaseSetup_part (resident : Program width 8)
    (channels nodes children guards roots base entry : Nat)
    (physical : ∀ phase : Fin (typedCopyColdCode width channels nodes children guards roots base entry).size,
      resident[entry + phase.val]? =
        (typedCopyColdCode width channels nodes children guards roots base entry)[phase.val]?) :
    ∀ phase : Fin 2, resident[(entry + 239) + phase.val]? =
      (typedReleaseSetupCode width (entry + 241))[phase.val]? := by
  let whole := typedCopyColdCode width channels nodes children guards roots base entry
  let before : Program width 8 := orderedTypedCopyCode width nodes children base entry (entry + 207) ++ typedOriginRecoverCode width nodes base ++ typedRuntimeSaveSetupCode width (entry + 233) ++ RawTransferLoops.reverseSaveCode width (entry + 233) (entry + 239)
  let fragment := typedReleaseSetupCode width (entry + 241)
  let after : Program width 8 := RawTransferLoops.countedReleaseCode width (entry + 241) (entry + 245) ++ typedColdHandoffCode width (entry + 247) ++ (typedShapeCode width channels nodes children guards roots).map (RawAdapterProgram.relocatedInstruction (entry + 247))
  have layout : whole = (before ++ fragment) ++ after := by
    dsimp only [whole, before, fragment, after]
    unfold typedCopyColdCode
    simp only [Array.append_assoc, Array.empty_append]
  have beforeSize : before.size = 239 := by
    dsimp only [before]
    simp only [Array.size_append, Array.size_empty, orderedTypedCopyCode_size,
      typedOriginRecoverCode_size, typedRuntimeSaveSetupCode_size,
      RawTransferLoops.reverseSaveCode_size, typedReleaseSetupCode_size,
      RawTransferLoops.countedReleaseCode_size, typedColdHandoffCode_size]
  have fragmentSize : fragment.size = 2 := by
    dsimp only [fragment]
    simp only [typedReleaseSetupCode_size]
  exact extract_copy_section resident whole before fragment after entry 239 2
    layout beforeSize fragmentSize physical

private theorem typed_caller_release_part (resident : Program width 8)
    (channels nodes children guards roots base entry : Nat)
    (physical : ∀ phase : Fin (typedCopyColdCode width channels nodes children guards roots base entry).size,
      resident[entry + phase.val]? =
        (typedCopyColdCode width channels nodes children guards roots base entry)[phase.val]?) :
    ∀ phase : Fin 4, resident[(entry + 241) + phase.val]? =
      (RawTransferLoops.countedReleaseCode width (entry + 241) (entry + 245))[phase.val]? := by
  let whole := typedCopyColdCode width channels nodes children guards roots base entry
  let before : Program width 8 := orderedTypedCopyCode width nodes children base entry (entry + 207) ++ typedOriginRecoverCode width nodes base ++ typedRuntimeSaveSetupCode width (entry + 233) ++ RawTransferLoops.reverseSaveCode width (entry + 233) (entry + 239) ++ typedReleaseSetupCode width (entry + 241)
  let fragment := RawTransferLoops.countedReleaseCode width (entry + 241) (entry + 245)
  let after : Program width 8 := typedColdHandoffCode width (entry + 247) ++ (typedShapeCode width channels nodes children guards roots).map (RawAdapterProgram.relocatedInstruction (entry + 247))
  have layout : whole = (before ++ fragment) ++ after := by
    dsimp only [whole, before, fragment, after]
    unfold typedCopyColdCode
    simp only [Array.append_assoc, Array.empty_append]
  have beforeSize : before.size = 241 := by
    dsimp only [before]
    simp only [Array.size_append, Array.size_empty, orderedTypedCopyCode_size,
      typedOriginRecoverCode_size, typedRuntimeSaveSetupCode_size,
      RawTransferLoops.reverseSaveCode_size, typedReleaseSetupCode_size,
      RawTransferLoops.countedReleaseCode_size, typedColdHandoffCode_size]
  have fragmentSize : fragment.size = 4 := by
    dsimp only [fragment]
    simp only [RawTransferLoops.countedReleaseCode_size]
  exact extract_copy_section resident whole before fragment after entry 241 4
    layout beforeSize fragmentSize physical

private theorem typed_caller_handoff_part (resident : Program width 8)
    (channels nodes children guards roots base entry : Nat)
    (physical : ∀ phase : Fin (typedCopyColdCode width channels nodes children guards roots base entry).size,
      resident[entry + phase.val]? =
        (typedCopyColdCode width channels nodes children guards roots base entry)[phase.val]?) :
    ∀ phase : Fin 2, resident[(entry + 245) + phase.val]? =
      (typedColdHandoffCode width (entry + 247))[phase.val]? := by
  let whole := typedCopyColdCode width channels nodes children guards roots base entry
  let before : Program width 8 := orderedTypedCopyCode width nodes children base entry (entry + 207) ++ typedOriginRecoverCode width nodes base ++ typedRuntimeSaveSetupCode width (entry + 233) ++ RawTransferLoops.reverseSaveCode width (entry + 233) (entry + 239) ++ typedReleaseSetupCode width (entry + 241) ++ RawTransferLoops.countedReleaseCode width (entry + 241) (entry + 245)
  let fragment := typedColdHandoffCode width (entry + 247)
  let after : Program width 8 := (typedShapeCode width channels nodes children guards roots).map (RawAdapterProgram.relocatedInstruction (entry + 247))
  have layout : whole = (before ++ fragment) ++ after := by
    dsimp only [whole, before, fragment, after]
    unfold typedCopyColdCode
    simp only [Array.append_assoc, Array.empty_append]
  have beforeSize : before.size = 245 := by
    dsimp only [before]
    simp only [Array.size_append, Array.size_empty, orderedTypedCopyCode_size,
      typedOriginRecoverCode_size, typedRuntimeSaveSetupCode_size,
      RawTransferLoops.reverseSaveCode_size, typedReleaseSetupCode_size,
      RawTransferLoops.countedReleaseCode_size, typedColdHandoffCode_size]
  have fragmentSize : fragment.size = 2 := by
    dsimp only [fragment]
    simp only [typedColdHandoffCode_size]
  exact extract_copy_section resident whole before fragment after entry 245 2
    layout beforeSize fragmentSize physical

private theorem typed_caller_cold_part (resident : Program width 8)
    (channels nodes children guards roots base entry : Nat)
    (physical : ∀ phase : Fin (typedCopyColdCode width channels nodes children guards roots base entry).size,
      resident[entry + phase.val]? =
        (typedCopyColdCode width channels nodes children guards roots base entry)[phase.val]?) :
    ∀ index (valid : index < (typedShapeCode width channels nodes children guards roots).size),
      resident[(entry + 247) + index]? = some
        (RawAdapterProgram.relocatedInstruction (entry + 247)
          ((typedShapeCode width channels nodes children guards roots)[index]'valid)) := by
  let whole := typedCopyColdCode width channels nodes children guards roots base entry
  let before := orderedTypedCopyCode width nodes children base entry (entry + 207) ++
    typedOriginRecoverCode width nodes base ++
    typedRuntimeSaveSetupCode width (entry + 233) ++
    RawTransferLoops.reverseSaveCode width (entry + 233) (entry + 239) ++
    typedReleaseSetupCode width (entry + 241) ++
    RawTransferLoops.countedReleaseCode width (entry + 241) (entry + 245) ++
    typedColdHandoffCode width (entry + 247)
  let fragment := (typedShapeCode width channels nodes children guards roots).map
    (RawAdapterProgram.relocatedInstruction (entry + 247))
  have layout : whole = (before ++ fragment) ++ #[] := by
    dsimp only [whole, before, fragment]
    unfold typedCopyColdCode
    simp only [Array.append_empty]
  have beforeSize : before.size = 247 := by
    dsimp only [before]
    simp only [Array.size_append, orderedTypedCopyCode_size,
      typedOriginRecoverCode_size, typedRuntimeSaveSetupCode_size,
      RawTransferLoops.reverseSaveCode_size, typedReleaseSetupCode_size,
      RawTransferLoops.countedReleaseCode_size, typedColdHandoffCode_size]
  have fragmentSize : fragment.size =
      (typedShapeCode width channels nodes children guards roots).size := by
    dsimp only [fragment]
    exact Array.size_map
  have selected := extract_copy_section resident whole before fragment #[] entry 247
    (typedShapeCode width channels nodes children guards roots).size layout beforeSize fragmentSize physical
  intro index valid
  have cell := selected ⟨index, valid⟩
  change resident[(entry + 247) + index]? = fragment[index]? at cell
  rw [show fragment[index]? = some (RawAdapterProgram.relocatedInstruction (entry + 247)
    ((typedShapeCode width channels nodes children guards roots)[index]'valid)) from by
      dsimp only [fragment]
      rw [Array.getElem?_map, Array.getElem?_eq_getElem valid]
      rfl] at cell
  exact cell

-- Used directly when appending the actual ordered copy to the runtime cold trace.
private theorem ordered_runtime_tick_bound (V E U R H G coneWork copyTicks coldTicks : Nat)
    (copyBound : copyTicks ≤ 119 * V + 9 * E + 7 * U + 9 * R + 68)
    (coldBound : coldTicks ≤ 6 * (5 + 6 * V + E + U + R) +
      4 * (H + (5 + 6 * V + E + U + R)) + 142 * G + 226 * coneWork + 76)
    (incidences : V + E + U + R ≤ G) :
    copyTicks + coldTicks ≤ 321 * G + 4 * H + 226 * coneWork + 194 := by
  omega


/-- The assembled ordered copy, counted transfer, and typed evaluator execute
from the retained source and the rank table produced by dependency ordering. -/
theorem ordered_copy_runtime_cold_execution (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (assignment : Assignment channels)
    (suffix : List (Word (typedExecutionWidth numbering.toDAG)))
    (resident : Program (typedExecutionWidth numbering.toDAG) 8)
    (initial : State (typedExecutionWidth numbering.toDAG) 8)
    (H base rankBase entry : Nat)
    (image : OriginalImageStored initial.heap H channels raw)
    (rawCell : initial.heap[Controller.Horn.WorklistFIFO.activeSlot (n := raw.nodes.size) base]? =
      some (word (typedExecutionWidth numbering.toDAG) H))
    (queue : ∀ index : Fin numbering.order.length,
      initial.heap[Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base + index.val]? =
        some (word (typedExecutionWidth numbering.toDAG) (numbering.order[index.val].val)))
    (ranks : ∀ index : Fin numbering.order.length,
      initial.heap[rankBase + numbering.order[index.val].val]? =
        some (word (typedExecutionWidth numbering.toDAG) index.val))
    (physical : ∀ phase : Fin (typedCopyColdCode (typedExecutionWidth numbering.toDAG)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length base entry).size,
      resident[entry + phase.val]? =
        (typedCopyColdCode (typedExecutionWidth numbering.toDAG) channels raw.nodes.size
          (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
          raw.roots.length base entry)[phase.val]?)
    (position : initial.pc = word (typedExecutionWidth numbering.toDAG) entry)
    (running : initial.halted = false)
    (codeFits : entry + (typedCopyColdCode (typedExecutionWidth numbering.toDAG)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length base entry).size <
      2 ^ typedExecutionWidth numbering.toDAG)
    (capacity : channels + initial.heap.size +
      (numberedPacketWords (width := typedExecutionWidth numbering.toDAG) raw valid numbering).length <
      2 ^ typedExecutionWidth numbering.toDAG)
    (allocation : initial.heap.size = rankBase + raw.nodes.size)
    (rankHeld : initial.reg 4 = word (typedExecutionWidth numbering.toDAG) rankBase)
    (scratchBefore : base + 4 * raw.nodes.size + 4 ≤ H)
    (rankAfter : H ≤ rankBase)
    (inputStack : initial.stack = List.ofFn
      (fun channel => boolWord (typedExecutionWidth numbering.toDAG) (assignment channel)) ++ suffix) :
    ∃ final ticks peak, Execution resident initial final ticks peak ∧
      ticks ≤ 321 * numbering.toDAG.countedSize + 4 * initial.heap.size +
        226 * (numbering.toDAG.roots.map (typedConeIncidenceSize numbering.toDAG)).sum + 194 ∧
      peak ≤ max (initial.liveWords +
        2 * (numberedPacketWords (width := typedExecutionWidth numbering.toDAG) raw valid numbering).length)
        (38 * numbering.toDAG.countedSize + 1884 + suffix.length + initial.output.length) ∧
      final.stack = suffix ∧
      final.output = (numbering.toDAG.roots.map (fun node =>
        boolWord (typedExecutionWidth numbering.toDAG) (numbering.toDAG.eval assignment node))).reverse ++
        initial.output ∧ final.halted = true := by
  let graph := numbering.toDAG
  let rows := numberedRows raw valid numbering
  let roots := graph.roots.map Fin.val
  let E := (rowChildren (originalRows raw)).length
  let U := (rowGuards (originalRows raw)).length
  let L := (numberedPacketWords (width := typedExecutionWidth graph) raw valid numbering).length
  change entry + (typedCopyColdCode (typedExecutionWidth graph) channels raw.nodes.size
    E U raw.roots.length base entry).size < 2 ^ typedExecutionWidth graph at codeFits
  change channels + initial.heap.size + L < 2 ^ typedExecutionWidth graph at capacity
  have matched : RowsMatch graph rows := numbered_rows_match raw valid numbering
  have heads : UniformDAGSource.HeadsMatch graph rows matched := numbered_rows_heads raw valid numbering
  have rootMatches : RootsMatch graph roots := rfl
  have nodesEq : graph.nodeCount = raw.nodes.size := by
    change numbering.toDAG.nodeCount = raw.nodes.size
    exact numbering.toDAG_nodeCount
  have rootsEq : graph.roots.length = raw.roots.length := RawNumberingCounts.numbered_roots raw valid numbering
  have sourceCounts : (rowChildren rows).length = E ∧ (rowGuards rows).length = U :=
    numbered_incidence_image raw valid numbering
  have graphCounts := matched_incidence_lengths graph rows matched
  have childEq : graph.childIncidences = E := graphCounts.1.symm.trans sourceCounts.1
  have guardEq : graph.guardIncidences = U := graphCounts.2.symm.trans sourceCounts.2
  have packetEq : numberedPacketWords (width := typedExecutionWidth graph) raw valid numbering =
      typedPacketWords graph rows roots := numbered_cold_input_words raw valid numbering
  have lengthEq : L = 5 + 6 * raw.nodes.size + E + U + raw.roots.length := by
    have counted := typed_input_length graph rows roots matched rootMatches
    rw [← packetEq] at counted
    simpa only [L, nodesEq, childEq, guardEq, rootsEq] using counted
  have shapeSize : 247 ≤ (typedCopyColdCode (typedExecutionWidth graph)
      channels raw.nodes.size E U raw.roots.length base entry).size := by
    rw [typedCopyColdCode_size]
    omega
  obtain ⟨copied, copyTicks, copyPeak, copyTrace, copyTime, copySpace, copyPC, copyRunning,
      copiedCells, copiedSize, retainedImage, retainedQueue, retainedRanks, copiedStack,
      copiedOutput, copiedRank, copiedZero, copiedMask, originCell⟩ :=
    ordered_copy_execution resident raw valid numbering initial H base rankBase entry (entry + 207)
      image rawCell queue ranks
      (typed_caller_copy_part resident channels raw.nodes.size E U raw.roots.length base entry physical)
      position running (by change entry + 207 < 2 ^ typedExecutionWidth graph; omega)
      capacity allocation rankHeld scratchBefore rankAfter
  have typedCells : CopiedPacketCells copied.heap initial.heap.size (typedPacketWords graph rows roots) := by
    rw [← packetEq]
    exact copiedCells
  have typedAllocation : copied.heap.size = initial.heap.size + (typedPacketWords graph rows roots).length := by
    rw [← packetEq]
    exact copiedSize
  have typedStack : copied.stack = List.ofFn
      (fun channel => boolWord (typedExecutionWidth graph) (assignment channel)) ++ suffix :=
    copiedStack.trans inputStack
  have coldPhysical : ∀ index (validIndex : index <
      (typedShapeCode (typedExecutionWidth graph) channels graph.nodeCount
        (rowChildren rows).length (rowGuards rows).length roots.length).size),
      resident[(entry + 247) + index]? = some
        (RawAdapterProgram.relocatedInstruction (entry + 247)
          ((typedShapeCode (typedExecutionWidth graph) channels graph.nodeCount
            (rowChildren rows).length (rowGuards rows).length roots.length)[index]'validIndex)) := by
    simpa only [nodesEq, sourceCounts.1, sourceCounts.2, roots, List.length_map, rootsEq] using
      typed_caller_cold_part resident channels raw.nodes.size E U raw.roots.length base entry physical
  have saveAt : RawTransferLoops.CodeAt resident (entry + 233)
      (RawTransferLoops.reverseSaveCode (typedExecutionWidth graph) (entry + 233) (entry + 239)) := by
    intro phase
    exact typed_caller_save_part resident channels raw.nodes.size E U raw.roots.length base entry physical
      ⟨phase.val, by simpa only [RawTransferLoops.reverseSaveCode_size] using phase.isLt⟩
  have releaseAt : RawTransferLoops.CodeAt resident (entry + 241)
      (RawTransferLoops.countedReleaseCode (typedExecutionWidth graph) (entry + 241) (entry + 245)) := by
    intro phase
    exact typed_caller_release_part resident channels raw.nodes.size E U raw.roots.length base entry physical
      ⟨phase.val, by simpa only [RawTransferLoops.countedReleaseCode_size] using phase.isLt⟩
  have coldFits : entry + 247 + (typedShapeCode (typedExecutionWidth graph) channels graph.nodeCount
      (rowChildren rows).length (rowGuards rows).length roots.length).size <
      2 ^ typedExecutionWidth graph := by
    have wholeFits := codeFits
    rw [typedCopyColdCode_size] at wholeFits
    simpa only [nodesEq, sourceCounts.1, sourceCounts.2, roots, List.length_map, rootsEq,
      Nat.add_assoc] using wholeFits
  obtain ⟨final, coldTicks, coldPeak, coldTrace, coldTime, coldSpace, finalStack,
      finalOutput, finalHalted⟩ :=
    copied_packet_runtime_cold_execution graph rows roots matched heads rootMatches assignment suffix
      resident raw.nodes.size base initial.heap.size (entry + 207) (entry + 209) (entry + 233)
      (entry + 239) (entry + 241) (entry + 245) (entry + 247) copied
      (typed_caller_recover_part resident channels raw.nodes.size E U raw.roots.length base entry physical)
      (typed_caller_runtime_part resident channels raw.nodes.size E U raw.roots.length base entry physical)
      saveAt
      (typed_caller_releaseSetup_part resident channels raw.nodes.size E U raw.roots.length base entry physical)
      releaseAt
      (typed_caller_handoff_part resident channels raw.nodes.size E U raw.roots.length base entry physical)
      coldPhysical (by omega) copyPC copyRunning (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) coldFits
      (by omega)
      (by rw [← packetEq]; change 0 < L; omega)
      (by rw [← packetEq]; exact Nat.lt_of_le_of_lt (by omega) capacity)
      typedAllocation
      (by unfold Controller.Horn.WorklistBucketReady.nextSlot; omega)
      originCell typedCells copiedZero copiedMask typedStack
  have copiedLive : copied.liveWords = initial.liveWords + L := by
    simp only [State.liveWords, copiedSize, copiedStack, copiedOutput, L]
    omega
  have joined := copyTrace.append coldTrace
  refine ⟨final, copyTicks + coldTicks, max copyPeak coldPeak, joined, ?_, ?_,
    finalStack, finalOutput.trans (by rw [copiedOutput]), finalHalted⟩
  · have incidenceBound : raw.nodes.size + E + U + raw.roots.length ≤ graph.countedSize := by
      have counted : graph.countedSize = channels + raw.nodes.size + E + U + raw.roots.length := by
        simpa only [nodesEq, childEq, guardEq, rootsEq] using graph.countedSize_eq
      omega
    have runtimeBound : coldTicks ≤ 6 * (5 + 6 * raw.nodes.size + E + U + raw.roots.length) +
        4 * (initial.heap.size + (5 + 6 * raw.nodes.size + E + U + raw.roots.length)) +
        142 * graph.countedSize + 226 * (graph.roots.map (typedConeIncidenceSize graph)).sum + 76 := by
      rw [← packetEq, copiedSize] at coldTime
      change coldTicks ≤ 6 * L + 4 * (initial.heap.size + L) +
        142 * graph.countedSize + 226 * (graph.roots.map (typedConeIncidenceSize graph)).sum + 76 at coldTime
      rw [lengthEq] at coldTime
      exact coldTime
    exact ordered_runtime_tick_bound raw.nodes.size E U raw.roots.length initial.heap.size
      graph.countedSize (graph.roots.map (typedConeIncidenceSize graph)).sum copyTicks coldTicks
      copyTime runtimeBound incidenceBound
  · change max copyPeak coldPeak ≤ max (initial.liveWords + 2 * L)
      (38 * graph.countedSize + 1884 + suffix.length + initial.output.length)
    change copyPeak ≤ initial.liveWords + L at copySpace
    rw [max_le_iff]
    constructor
    · exact le_trans copySpace (le_trans (by omega) (le_max_left _ _))
    · rw [copiedLive, copiedOutput, ← packetEq] at coldSpace
      change coldPeak ≤ max (initial.liveWords + L + L)
        (38 * graph.countedSize + 1884 + suffix.length + initial.output.length) at coldSpace
      exact le_trans coldSpace (by apply max_le_max <;> omega)


theorem accepted_queue_complete (graph : UnorderedDAG channels)
    (queue : List (Fin graph.nodeCount)) (distinct : queue.Nodup)
    (lengthEq : queue.length = graph.nodeCount) : ∀ node, node ∈ queue := by
  have counted : queue.toFinset.card = Fintype.card (Fin graph.nodeCount) := by
    rw [List.toFinset_card_of_nodup distinct, Fintype.card_fin, lengthEq]
  have exhaustive : queue.toFinset = Finset.univ :=
    (Finset.card_eq_iff_eq_univ queue.toFinset).mp counted
  intro node
  apply List.mem_toFinset.mp
  rw [exhaustive]
  exact Finset.mem_univ node

private def sourceRankNarrow (state : State width 8) : State width 4 :=
  { reg := fun register => state.reg (Controller.Cost.RegisterWiden.widenRegister register)
    heap := state.heap, stack := state.stack, output := state.output,
    pc := state.pc, halted := state.halted }

private theorem sourceRankWidenNarrow (state : State width 8) :
    Controller.Cost.RegisterWiden.widenState (sourceRankNarrow state) state.reg = state := by
  have registers : (Controller.Cost.RegisterWiden.widenState (sourceRankNarrow state) state.reg).reg = state.reg := by
    funext register
    by_cases small : register.val < 4
    · change (if h : register.val < 4 then
        state.reg (Controller.Cost.RegisterWiden.widenRegister ⟨register.val, h⟩) else state.reg register) = state.reg register
      rw [dite_eq_left small]
      have same : Controller.Cost.RegisterWiden.widenRegister ⟨register.val, small⟩ = register := Fin.ext rfl
      rw [same]
    · simp only [Controller.Cost.RegisterWiden.widenState, dite_eq_right small]
  cases state
  simp only [Controller.Cost.RegisterWiden.widenState, sourceRankNarrow] at registers ⊢
  congr 1



private theorem source_rank_appended_cell (original final : Array (Word width))
    (added : Array (Word width)) (same : final = original ++ added)
    (address : Nat) (value : Word width) (cell : original[address]? = some value) :
    final[address]? = some value := by
  obtain ⟨inside, actual⟩ := Array.getElem?_eq_some_iff.mp cell
  rw [same, Array.getElem?_append_left inside]
  exact cell



private theorem source_rank_reload_execution (resident : Program width 8) (entry : Nat)
    (state : State width 8) (packet suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = word width state.heap.size :: (packet ++ suffix))
    (popAt : resident[entry]? = some (.pop 4))
    (reloadAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident (entry + 1)
      (Controller.Cost.InputLoad.code (width := width) packet.length))
    (capacity : entry + 1 + 2 * packet.length < 2 ^ width)
    (room : state.heap.size + packet.length ≤ 2 ^ width) :
    ∃ final, Execution resident state final (1 + 2 * packet.length) state.liveWords ∧
      final.heap = state.heap ++ packet.toArray ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.reg 4 = word width state.heap.size ∧
      final.pc = word width (entry + 1 + 2 * packet.length) ∧ final.halted = false ∧
      (∀ address, address < state.heap.size → final.heap[address]? = state.heap[address]?) := by
  let restored : State width 8 := { state.advance.put 4 (word width state.heap.size)
    with stack := packet ++ suffix }
  have transition : programStep resident state = some restored := by
    rw [fetched resident state entry (.pop 4) position (by omega) popAt]
    simp only [step, running, Bool.false_eq_true, ite_false, saved, restored]
  have restoredPC : restored.pc = word width (entry + 1) :=
    referenceAdvancePC state entry position (by omega)
  have restoredLive : restored.liveWords + 1 = state.liveWords := by
    simp only [restored, State.liveWords, State.advance, State.put, saved,
      List.length_cons, List.length_append]
    omega
  have popTrace : Execution resident state restored 1 state.liveWords := by
    have trace := Execution.cons transition (Execution.refl restored)
    simpa only [show max state.liveWords restored.liveWords = state.liveWords from
      Nat.max_eq_left (by omega), Nat.reduceAdd] using trace
  obtain ⟨final, reloadTrace, heap, stack, output, pc, active, registers, retained⟩ :=
    RawAdapterProgram.source_reload_execution resident (entry + 1) restored packet suffix restoredPC running rfl
      (by omega) room reloadAt
  refine ⟨final, ?_, heap, stack, output, ?_, pc, active, retained⟩
  · simpa only [show max state.liveWords restored.liveWords = state.liveWords from
      Nat.max_eq_left (by omega)] using popTrace.append reloadTrace
  · exact registers 4 (by decide)

private theorem source_rank_zero_execution (resident : Program width 8) (entry nodes : Nat)
    (state : State width 8) (position : state.pc = word width entry)
    (running : state.halted = false) (codeFits : entry + 2 * nodes < 2 ^ width)
    (room : state.heap.size + nodes ≤ 2 ^ width)
    (present : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident entry
      (Controller.Cost.Initialize.code (word width 0) nodes)) :
    ∃ final, Execution resident state final (2 * nodes) (state.liveWords + nodes) ∧
      final.heap = state.heap ++ (List.replicate nodes (word width 0)).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 2 * nodes) ∧ final.halted = false ∧
      (∀ register : Fin 8, 4 ≤ register.val → final.reg register = state.reg register) := by
  let low := sourceRankNarrow state
  let view := Controller.Cost.ForestZeroCallerWiden.lowerProgram resident
  have lowBlock := Controller.Cost.ForestZeroCallerWiden.lower_block resident entry
    (Controller.Cost.Initialize.code (word width 0) nodes) present
  obtain ⟨last, trace, heap, stack, output, pc, active⟩ :=
    Controller.Cost.Initialize.code_execution view low (word width 0) entry nodes
      position running codeFits room lowBlock
  have lifted := Controller.Cost.ForestZeroCallerWiden.execution resident low last
    (2 * nodes) (low.liveWords + nodes) trace active state.reg
  have sourceLive : low.liveWords + 4 = state.liveWords := by
    simp only [low, sourceRankNarrow, State.liveWords]
    omega
  let final := Controller.Cost.RegisterWiden.widenState last state.reg
  refine ⟨final, ?_, heap, stack, output, pc, active, ?_⟩
  · rw [sourceRankWidenNarrow] at lifted
    simpa only [show low.liveWords + nodes + 4 = state.liveWords + nodes by omega] using lifted
  · intro register high
    exact Controller.Cost.RegisterWiden.widenState_high last state.reg register high

-- The setup consumes the reloaded original source and the allocated V-zero rank table.
-- Register 4 is the popped, runtime-derived original index heap end H.
-- The raw source begins at H; its counted encoder size W is known before numbering.
-- The dead FIFO active header stores H while rankCopy uses register 4 for H+W.
def sourceRankSetupCode (width nodes base rawWords rankEntry : Nat) : Program width 8 :=
  #[.constant 5 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)),
    .store 5 4,
    .constant 5 (word width rawWords),
    .add 4 4 5,
    .constant 0 (word width nodes),
    .constant 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base)),
    .constant 2 (word width 0),
    .constant 3 (word width 1),
    .constant 6 (word width 0),
    .constant 7 (word width (2 ^ width - 1)),
    .branchZero 6 (word width rankEntry)]

-- Required consumer postcondition, derived by the eleven fetched instructions:
-- actual heap = (finished.heap ++ rawPacket.toArray ++ replicate V zero).setIfInBounds activeSlot (word H)
-- actual reg4 = word(H+W), reg1 = queueStart, reg2=0, reg0=V, reg3=1, reg6=0, reg7=mask.
-- rankBase+V=heap.size and prefix Q cells unchanged because activeSlot<queueStart.
-- Source cells [H,H+W) and new rank zero cells [H+W,H+W+V) remain exact.
-- Cost 11 ticks, no allocation, liveWords unchanged. Followed by existing RawAdapterProgram.rank_copy_execution:
-- 8V+1 ticks after actual accepted Q.length=V; old rank and original numbering derived from QStored.
-- No supplied rank oracle and no program immediate depending on H or deduplicated occurrence count.

private theorem source_rank_setup_execution (resident : Program width 8)
    (entry nodes base rawWords rankEntry heapEnd : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 11 < 2 ^ width)
    (rankFits : heapEnd + rawWords < 2 ^ width)
    (headerFits : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < 2 ^ width)
    (headerBound : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < state.heap.size)
    (held : state.reg 4 = word width heapEnd)
    (physical : ∀ phase : Fin 11, resident[entry + phase.val]? =
      (sourceRankSetupCode width nodes base rawWords rankEntry)[phase.val]?) :
    ∃ final, Execution resident state final 11 state.liveWords ∧
      final.heap = state.heap.set
        (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base) (word width heapEnd) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width rankEntry ∧ final.halted = false ∧
      final.reg 0 = word width nodes ∧
      final.reg 1 = word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base) ∧
      final.reg 2 = word width 0 ∧ final.reg 3 = word width 1 ∧
      final.reg 4 = word width (heapEnd + rawWords) ∧
      final.reg 6 = word width 0 ∧ final.reg 7 = word width (2 ^ width - 1) := by
  let s1 := state.advance.put 5 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))
  let s2 : State width 8 := { s1.advance with heap :=
    (state.heap.set (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base) (word width heapEnd)) }
  let s3 := s2.advance.put 5 (word width rawWords)
  let s4 := s3.advance.put 4 (word width (heapEnd + rawWords))
  let s5 := s4.advance.put 0 (word width nodes)
  let s6 := s5.advance.put 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base))
  let s7 := s6.advance.put 2 (word width 0)
  let s8 := s7.advance.put 3 (word width 1)
  let s9 := s8.advance.put 6 (word width 0)
  let s10 := s9.advance.put 7 (word width (2 ^ width - 1))
  let final : State width 8 := { s10.advance with pc := word width rankEntry }
  have headerValue : (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)).val =
      Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base := Nat.mod_eq_of_lt headerFits
  have heapEndValue : (word width heapEnd).val = heapEnd := Nat.mod_eq_of_lt (by omega)
  have rawValue : (word width rawWords).val = rawWords := Nat.mod_eq_of_lt (by omega)
  have pc1 : s1.pc = word width (entry + 1) := by
    change state.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC state (entry + 0) position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    change s3.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s3 (entry + 3) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := by
    change s4.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s4 (entry + 4) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 6) := by
    change s5.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s5 (entry + 5) pc5 (by omega)
  have pc7 : s7.pc = word width (entry + 7) := by
    change s6.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s6 (entry + 6) pc6 (by omega)
  have pc8 : s8.pc = word width (entry + 8) := by
    change s7.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s7 (entry + 7) pc7 (by omega)
  have pc9 : s9.pc = word width (entry + 9) := by
    change s8.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s8 (entry + 8) pc8 (by omega)
  have pc10 : s10.pc = word width (entry + 10) := by
    change s9.advance.pc = _
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      referenceAdvancePC s9 (entry + 9) pc9 (by omega)
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.constant 5 (word width (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base))) position (by omega)
      (by simpa [sourceRankSetupCode] using physical ⟨0, by decide⟩)]
    simp [s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.store 5 4) pc1 (by omega)
      (by simpa [sourceRankSetupCode] using physical ⟨1, by decide⟩)]
    simp [s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.constant 5 (word width rawWords)) pc2 (by omega)
      (by simpa [sourceRankSetupCode] using physical ⟨2, by decide⟩)]
    simp [s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.add 4 4 5) pc3 (by omega)
      (by simpa [sourceRankSetupCode] using physical ⟨3, by decide⟩)]
    simp [s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.constant 0 (word width nodes)) pc4 (by omega)
      (by simpa [sourceRankSetupCode] using physical ⟨4, by decide⟩)]
    simp [s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.constant 1 (word width (Controller.Horn.WorklistMark.queueStart (n := nodes) base))) pc5 (by omega)
      (by simpa [sourceRankSetupCode] using physical ⟨5, by decide⟩)]
    simp [s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 2 (word width 0)) pc6 (by omega)
      (by simpa [sourceRankSetupCode] using physical ⟨6, by decide⟩)]
    simp [s7, s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.constant 3 (word width 1)) pc7 (by omega)
      (by simpa [sourceRankSetupCode] using physical ⟨7, by decide⟩)]
    simp [s8, s7, s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.constant 6 (word width 0)) pc8 (by omega)
      (by simpa [sourceRankSetupCode] using physical ⟨8, by decide⟩)]
    simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.constant 7 (word width (2 ^ width - 1))) pc9 (by omega)
      (by simpa [sourceRankSetupCode] using physical ⟨9, by decide⟩)]
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue]
  have t10 : programStep resident s10 = some final := by
    rw [fetched resident s10 (entry + 10) (.branchZero 6 (word width rankEntry)) pc10 (by omega)
      (by simpa [sourceRankSetupCode] using physical ⟨10, by decide⟩)]
    simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, final, step, State.advance, State.put, running, held,
      headerValue, headerBound, heapEndValue, rawValue, word]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.refl final)))))))))))
  have heapSize : (state.heap.set (Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base)
      (word width heapEnd)).size = state.heap.size := by simp
  have live1 : s1.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live2 : s2.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live3 : s3.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live4 : s4.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live5 : s5.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live6 : s6.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live7 : s7.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live8 : s8.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live9 : s9.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have live10 : s10.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  have finalLive : final.liveWords = state.liveWords := by
    simp only [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, Array.size_set]
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, finalLive, Nat.max_self,
      Nat.reduceAdd] using trace
  all_goals simp [final, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, State.advance, State.put]

-- Consumer separation facts used after actual source reload and rank zero append.


private theorem source_header_separated (nodes base heapEnd : Nat)
    (scratch : base + 4 * nodes + 4 ≤ heapEnd) :
    Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < heapEnd ∧
    Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base <
      Controller.Horn.WorklistMark.queueStart (n := nodes) base := by
  unfold Controller.Horn.WorklistFIFO.activeSlot Controller.Horn.WorklistMark.queueStart
  omega



theorem source_rank_execution (resident : Program width 8)
    (entry nodes base rankDone : Nat) (state : State width 8)
    (packet suffix : List (Word width)) (queue : List (Fin nodes))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = word width state.heap.size :: (packet ++ suffix))
    (complete : queue.length = nodes) (distinct : queue.Nodup)
    (scratch : base + 4 * nodes + 4 ≤ state.heap.size)
    (cells : ∀ index : Fin queue.length,
      state.heap[Controller.Horn.WorklistMark.queueStart (n := nodes) base + index.val]? =
        some (word width queue[index.val].val))
    (capacity : entry + 1 + 2 * packet.length + 2 * nodes + 11 + 8 < 2 ^ width)
    (room : state.heap.size + packet.length + nodes < 2 ^ width)
    (popAt : resident[entry]? = some (.pop 4))
    (reloadAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident (entry + 1)
      (Controller.Cost.InputLoad.code (width := width) packet.length))
    (zeroAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident
      (entry + 1 + 2 * packet.length) (Controller.Cost.Initialize.code (word width 0) nodes))
    (setupAt : ∀ phase : Fin 11,
      resident[(entry + 1 + 2 * packet.length + 2 * nodes) + phase.val]? =
        (sourceRankSetupCode width nodes base packet.length
          (entry + 1 + 2 * packet.length + 2 * nodes + 11))[phase.val]?)
    (rankAt : ∀ phase : Fin 8,
      resident[(entry + 1 + 2 * packet.length + 2 * nodes + 11) + phase.val]? =
        (RawAdapterProgram.rankCopyCode width (entry + 1 + 2 * packet.length + 2 * nodes + 11) rankDone)[phase.val]?) :
    ∃ final peak, Execution resident state final (2 * packet.length + 10 * nodes + 13) peak ∧
      peak ≤ state.liveWords + nodes ∧ final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width rankDone ∧ final.halted = false ∧
      final.reg 4 = word width (state.heap.size + packet.length) ∧
      final.heap.size = state.heap.size + packet.length + nodes ∧
      (∀ index : Fin queue.length,
        final.heap[Controller.Horn.WorklistMark.queueStart (n := nodes) base + index.val]? =
          some (word width queue[index.val].val)) ∧
      (∀ index : Fin packet.length,
        final.heap[state.heap.size + index.val]? = some packet[index.val]) ∧
      (∀ index : Fin queue.length,
        final.heap[state.heap.size + packet.length + queue[index.val].val]? = some (word width index.val)) ∧
      final.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? =
        some (word width state.heap.size) := by
  obtain ⟨loaded, loadTrace, loadedHeap, loadedStack, loadedOutput, loadedBase,
    loadedPC, loadedRunning, loadRetained⟩ := source_rank_reload_execution resident entry state packet suffix
      position running saved popAt reloadAt (by omega) (by omega)
  have loadedSize : loaded.heap.size = state.heap.size + packet.length := by
    rw [loadedHeap]; simp
  obtain ⟨zeroed, zeroTrace, zeroHeap, zeroStack, zeroOutput, zeroPC, zeroRunning, zeroRegisters⟩ :=
    source_rank_zero_execution resident (entry + 1 + 2 * packet.length) nodes loaded
      loadedPC loadedRunning (by omega) (by omega) zeroAt
  have zeroSize : zeroed.heap.size = state.heap.size + packet.length + nodes := by
    rw [zeroHeap]
    simp only [Array.size_append, List.size_toArray, List.length_replicate, loadedSize]
  have zeroBase : zeroed.reg 4 = word width state.heap.size :=
    (zeroRegisters 4 (by decide)).trans loadedBase
  have activeFits : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < 2 ^ width := by
    have := (source_header_separated nodes base state.heap.size scratch).1
    omega
  have activeBound : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base < zeroed.heap.size := by
    have := (source_header_separated nodes base state.heap.size scratch).1
    omega
  obtain ⟨started, setupTrace, setupHeap, setupStack, setupOutput, setupPC, setupRunning,
    countReg, cursorReg, rankReg, oneReg, baseReg, zeroReg, maskReg⟩ := source_rank_setup_execution
      resident (entry + 1 + 2 * packet.length + 2 * nodes) nodes base packet.length
      (entry + 1 + 2 * packet.length + 2 * nodes + 11) state.heap.size zeroed
      zeroPC zeroRunning (by omega) (by omega) activeFits activeBound zeroBase setupAt
  have startedSize : started.heap.size = state.heap.size + packet.length + nodes := by
    rw [setupHeap]; simpa using zeroSize
  have sourceCell : ∀ address value, state.heap[address]? = some value →
      address ≠ Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base → started.heap[address]? = some value := by
    intro address value original different
    have first := source_rank_appended_cell state.heap loaded.heap packet.toArray loadedHeap address value original
    have second := source_rank_appended_cell loaded.heap zeroed.heap
      (List.replicate nodes (word width 0)).toArray zeroHeap address value first
    rw [setupHeap, Array.getElem?_set activeBound, ite_eq_right (Ne.symm different)]
    exact second
  have queueCells : ∀ index : Fin (queue.map Fin.val).length,
      started.heap[Controller.Horn.WorklistMark.queueStart (n := nodes) base + index.val]? =
        some (word width (queue.map Fin.val)[index.val]) := by
    intro index
    have bound : index.val < queue.length := by simpa using index.isLt
    have cell := cells ⟨index.val, bound⟩
    have different : Controller.Horn.WorklistMark.queueStart (n := nodes) base + index.val ≠
        Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base := by
      have := (source_header_separated nodes base state.heap.size scratch).2
      omega
    simpa using sourceCell _ _ cell different
  obtain ⟨final, rankTrace, rankHeap, rankStack, rankOutput, rankPC, rankRunning,
    finalCount, finalCursor, finalRank, rankRegisters, rankRetained⟩ := RawAdapterProgram.rank_copy_execution
      resident (entry + 1 + 2 * packet.length + 2 * nodes + 11) rankDone
      (state.heap.size + packet.length) nodes rankAt (by omega) (queue.map Fin.val)
      (by intro old member; obtain ⟨label, _, rfl⟩ := List.mem_map.mp member; exact label.isLt)
      (Controller.Horn.WorklistMark.queueStart (n := nodes) base) 0 started
      setupPC setupRunning (by simpa [complete] using countReg) cursorReg rankReg oneReg baseReg zeroReg maskReg
      (by simp only [List.length_map, complete]; omega)
      (by simp only [List.length_map, complete]; unfold Controller.Horn.WorklistMark.queueStart; omega)
      (by simp only [List.length_map, complete]; omega) (by omega) (by omega) queueCells
  have loadedLive : loaded.liveWords + 1 = state.liveWords := by
    unfold State.liveWords
    rw [loadedHeap, loadedStack, loadedOutput, saved]
    simp only [Array.size_append, List.size_toArray, List.length_append, List.length_cons]
    omega
  have zeroLive : zeroed.liveWords = loaded.liveWords + nodes := by
    unfold State.liveWords
    rw [zeroHeap, zeroStack, zeroOutput]
    simp <;> omega
  have startedLive : started.liveWords = zeroed.liveWords := by
    unfold State.liveWords
    rw [setupHeap, setupStack, setupOutput]
    simp
  have full := ((loadTrace.append zeroTrace).append setupTrace).append rankTrace
  have wholeTrace : Execution resident state final (2 * packet.length + 10 * nodes + 13)
      (max (max (max state.liveWords (loaded.liveWords + nodes)) zeroed.liveWords) started.liveWords) := by
    convert full using 1 <;> simp only [List.length_map, complete] <;> omega
  have actualEndCell : final.heap[Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base]? =
      some (word width state.heap.size) := by
    have activeBefore : Controller.Horn.WorklistFIFO.activeSlot (n := nodes) base <
        state.heap.size + packet.length := by
      have := (source_header_separated nodes base state.heap.size scratch).1
      omega
    rw [rankRetained _ activeBefore, setupHeap, Array.getElem?_set activeBound, ite_eq_left rfl]
  obtain ⟨certified, certifiedPeak, certifiedTrace, certifiedSpace, certifiedStack,
    certifiedOutput, certifiedPC, certifiedRunning, certifiedBase, certifiedSize,
    certifiedQueue, certifiedPacket, certifiedRanks⟩ :=
    RawAdapterProgram.accepted_rank_execution resident entry nodes base rankDone state packet suffix queue
      position running saved complete distinct scratch cells capacity room popAt reloadAt zeroAt setupAt rankAt
  have sameEndpoint := Controller.Horn.JoinedRuleFrame.execution_endpoint_unique wholeTrace certifiedTrace
  refine ⟨certified, certifiedPeak, certifiedTrace, certifiedSpace, certifiedStack, certifiedOutput,
    certifiedPC, certifiedRunning, certifiedBase, certifiedSize, certifiedQueue, certifiedPacket,
    certifiedRanks, ?_⟩
  rw [← sameEndpoint]
  exact actualEndCell

/-- Reload the retained original packet, build the rank table from the stored
accepted queue, and execute the ordered copy and evaluation on that same state.
The original heap end is read from the saved stack word and stored by the real
rank-setup instructions. No rank table or copied source image is a premise. -/
theorem accepted_rank_copy_runtime_execution (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (assignment : Assignment channels)
    (suffix : List (Word (typedExecutionWidth numbering.toDAG)))
    (resident : Program (typedExecutionWidth numbering.toDAG) 8)
    (initial : State (typedExecutionWidth numbering.toDAG) 8)
    (base entry copyEntry : Nat)
    (position : initial.pc = word (typedExecutionWidth numbering.toDAG) entry)
    (running : initial.halted = false)
    (saved : initial.stack = word (typedExecutionWidth numbering.toDAG) initial.heap.size ::
      ((originalPacket (typedExecutionWidth numbering.toDAG) channels raw).toList ++
        (List.ofFn (fun channel => boolWord (typedExecutionWidth numbering.toDAG)
          (assignment channel)) ++ suffix)))
    (scratch : base + 4 * raw.nodes.size + 4 ≤ initial.heap.size)
    (queueCells : ∀ index : Fin numbering.order.length,
      initial.heap[Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base + index.val]? =
        some (word (typedExecutionWidth numbering.toDAG) numbering.order[index.val].val))
    (rankCapacity : entry + 2 * (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).size +
      2 * raw.nodes.size + 20 < 2 ^ typedExecutionWidth numbering.toDAG)
    (room : channels + initial.heap.size +
      (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).size + raw.nodes.size +
      (numberedPacketWords (width := typedExecutionWidth numbering.toDAG) raw valid numbering).length <
      2 ^ typedExecutionWidth numbering.toDAG)
    (popAt : resident[entry]? = some (.pop 4))
    (reloadAt : ForestZeroCallerWiden.WidenedBlockAt resident (entry + 1)
      (InputLoad.code (width := typedExecutionWidth numbering.toDAG)
        (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).size))
    (zeroAt : ForestZeroCallerWiden.WidenedBlockAt resident
      (entry + 1 + 2 * (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).size)
      (Initialize.code (word (typedExecutionWidth numbering.toDAG) 0) raw.nodes.size))
    (setupAt : ∀ phase : Fin 11,
      resident[(entry + 1 + 2 * (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).size +
        2 * raw.nodes.size) + phase.val]? =
      (sourceRankSetupCode (typedExecutionWidth numbering.toDAG) raw.nodes.size base
        (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).size
        (entry + 1 + 2 * (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).size +
          2 * raw.nodes.size + 11))[phase.val]?)
    (rankAt : ∀ phase : Fin 8,
      resident[(entry + 1 + 2 * (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).size +
        2 * raw.nodes.size + 11) + phase.val]? =
      (RawAdapterProgram.rankCopyCode (typedExecutionWidth numbering.toDAG)
        (entry + 1 + 2 * (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).size +
          2 * raw.nodes.size + 11) copyEntry)[phase.val]?)
    (copyAt : ∀ phase : Fin (typedCopyColdCode (typedExecutionWidth numbering.toDAG)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length base copyEntry).size,
      resident[copyEntry + phase.val]? =
        (typedCopyColdCode (typedExecutionWidth numbering.toDAG) channels raw.nodes.size
          (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
          raw.roots.length base copyEntry)[phase.val]?)
    (copyCapacity : copyEntry + (typedCopyColdCode (typedExecutionWidth numbering.toDAG)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length base copyEntry).size <
      2 ^ typedExecutionWidth numbering.toDAG) :
    ∃ final ticks peak, Execution resident initial final ticks peak ∧
      ticks ≤ 2 * (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).size +
        10 * raw.nodes.size + 321 * numbering.toDAG.countedSize +
        4 * (initial.heap.size + (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).size +
          raw.nodes.size) +
        226 * (numbering.toDAG.roots.map (typedConeIncidenceSize numbering.toDAG)).sum + 207 ∧
      peak ≤ max (initial.liveWords + raw.nodes.size +
          2 * (numberedPacketWords (width := typedExecutionWidth numbering.toDAG) raw valid numbering).length)
        (38 * numbering.toDAG.countedSize + 1884 + suffix.length + initial.output.length) ∧
      final.stack = suffix ∧
      final.output = (numbering.toDAG.roots.map (fun node =>
        boolWord (typedExecutionWidth numbering.toDAG) (numbering.toDAG.eval assignment node))).reverse ++
        initial.output ∧ final.halted = true := by
  let packet := (originalPacket (typedExecutionWidth numbering.toDAG) channels raw).toList
  let tailWords := List.ofFn (fun channel => boolWord (typedExecutionWidth numbering.toDAG)
    (assignment channel)) ++ suffix
  have complete : numbering.order.length = raw.nodes.size := numbering.length_eq_nodeCount
  obtain ⟨ranked, rankPeak, rankTrace, rankSpace, rankStack, rankOutput, rankPC, rankRunning,
      rankBase, rankSize, actualQueue, actualPacket, actualRanks, originalEndCell⟩ :=
    source_rank_execution resident entry raw.nodes.size base copyEntry initial packet tailWords
      numbering.order position running saved complete numbering.distinct scratch queueCells
      (by simp only [packet, Array.length_toList]; omega)
      (by simp only [packet, Array.length_toList]; omega)
      popAt (by simpa only [packet, Array.length_toList] using reloadAt)
      (by simpa only [packet, Array.length_toList] using zeroAt)
      (by simpa only [packet, Array.length_toList] using setupAt)
      (by simpa only [packet, Array.length_toList] using rankAt)
  have actualImage : OriginalImageStored ranked.heap initial.heap.size channels raw := by
    intro index
    simpa only [packet, Array.length_toList, Array.getElem_toList] using
      actualPacket ⟨index.val, by simpa only [packet, Array.length_toList] using index.isLt⟩
  obtain ⟨final, copyTicks, copyPeak, copyTrace, copyTime, copySpace,
      finalStack, finalOutput, finalHalted⟩ :=
    ordered_copy_runtime_cold_execution raw valid numbering assignment suffix resident ranked
      initial.heap.size base (initial.heap.size + packet.length) copyEntry actualImage
      originalEndCell actualQueue actualRanks copyAt rankPC rankRunning copyCapacity
      (by rw [rankSize]; simp only [packet, Array.length_toList]; omega)
      rankSize rankBase scratch (by omega) rankStack
  have rankedLive : ranked.liveWords + 1 = initial.liveWords + raw.nodes.size := by
    unfold State.liveWords
    rw [rankSize, rankStack, rankOutput, saved]
    simp only [List.length_cons, List.length_append, packet, tailWords, Array.length_toList]
    omega
  have joined := rankTrace.append copyTrace
  refine ⟨final, 2 * packet.length + 10 * raw.nodes.size + 13 + copyTicks,
    max rankPeak copyPeak, joined, ?_, ?_, finalStack,
    finalOutput.trans (by rw [rankOutput]), finalHalted⟩
  · rw [rankSize] at copyTime
    simp only [packet, Array.length_toList] at copyTime ⊢
    omega
  · rw [max_le_iff]
    constructor
    · exact le_trans rankSpace (le_trans (by omega) (le_max_left _ _))
    · exact le_trans copySpace (max_le_max (by omega) (by rw [rankOutput]))



/-- A justified logarithmic word width determined before dependency ordering. -/
def rawExecutionWidth (channels : Nat) (raw : RawDAG) : Nat :=
  Nat.log 2 (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
    (rowGuards (originalRows raw)).length + raw.roots.length + 1) + 13

private theorem numbering_execution_width (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    typedExecutionWidth numbering.toDAG = rawExecutionWidth channels raw := by
  have rowEq : RawNumberingCounts.rowOfGate = originalRow := by
    funext gate
    cases gate <;> rfl
  have rowsEq : RawNumberingCounts.rawRows raw = originalRows raw := by
    simp only [RawNumberingCounts.rawRows, originalRows, rowEq]
  unfold typedExecutionWidth rawExecutionWidth
  rw [RawNumberingCounts.numbered_size]
  simp only [RawNumberingCounts.rawChildren, RawNumberingCounts.rawGuards, rowsEq]

def sourceDependencyRuntimeCode (width nodes base entry conflict : Nat) : Program width 8 :=
  Controller.Horn.WorklistAccept.headSetupCode (n := nodes) width base (entry + 4) ++
  Controller.Horn.WorklistFIFO.fetchCode (n := nodes) width base (entry + 4) (entry + 61) (entry + 18) ++
  Controller.Horn.WorklistBucketLoop.code width (entry + 18) (entry + 56) (entry + 30) ++
  Controller.Horn.WorklistBucketReady.code (n := nodes) width base (entry + 30)
    (entry + 56) conflict (entry + 18) ++
  Controller.Horn.WorklistFIFO.advanceCode (n := nodes) width base (entry + 4)

def sourceCycleCode (width tail expected accept tag : Nat) : Program width 8 :=
  #[.constant 2 (word width tail), .load 0 2,
    .constant 1 (word width expected), .xor 0 0 1,
    .branchZero 0 (word width accept), .constant 0 (word width tag), .emit 0, .halt]

private theorem source_execution_final_live (resident : Program width 8)
    {initial final : State width 8} {ticks peak : Nat}
    (trace : Execution resident initial final ticks peak) : final.liveWords ≤ peak := by
  induction trace with
  | refl => exact Nat.le_refl _
  | cons transition rest ih => exact ih.trans (Nat.le_max_right _ _)



private def SourceRankCopyContract (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (executionWidth : Nat) : Prop :=
  ∀ (assignment : Assignment channels)
    (suffix : List (Word (executionWidth)))
    (resident : Program (executionWidth) 8)
    (initial : State (executionWidth) 8)
    (base entry copyEntry : Nat)
    (position : initial.pc = word (executionWidth) entry)
    (running : initial.halted = false)
    (saved : initial.stack = word (executionWidth) initial.heap.size ::
      ((originalPacket (executionWidth) channels raw).toList ++
        (List.ofFn (fun channel => boolWord (executionWidth)
          (assignment channel)) ++ suffix)))
    (scratch : base + 4 * raw.nodes.size + 4 ≤ initial.heap.size)
    (queueCells : ∀ index : Fin numbering.order.length,
      initial.heap[Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base + index.val]? =
        some (word (executionWidth) numbering.order[index.val].val))
    (rankCapacity : entry + 2 * (originalPacket (executionWidth) channels raw).size +
      2 * raw.nodes.size + 20 < 2 ^ executionWidth)
    (room : channels + initial.heap.size +
      (originalPacket (executionWidth) channels raw).size + raw.nodes.size +
      (numberedPacketWords (width := executionWidth) raw valid numbering).length <
      2 ^ executionWidth)
    (popAt : resident[entry]? = some (.pop 4))
    (reloadAt : ForestZeroCallerWiden.WidenedBlockAt resident (entry + 1)
      (InputLoad.code (width := executionWidth)
        (originalPacket (executionWidth) channels raw).size))
    (zeroAt : ForestZeroCallerWiden.WidenedBlockAt resident
      (entry + 1 + 2 * (originalPacket (executionWidth) channels raw).size)
      (Initialize.code (word (executionWidth) 0) raw.nodes.size))
    (setupAt : ∀ phase : Fin 11,
      resident[(entry + 1 + 2 * (originalPacket (executionWidth) channels raw).size +
        2 * raw.nodes.size) + phase.val]? =
      (sourceRankSetupCode (executionWidth) raw.nodes.size base
        (originalPacket (executionWidth) channels raw).size
        (entry + 1 + 2 * (originalPacket (executionWidth) channels raw).size +
          2 * raw.nodes.size + 11))[phase.val]?)
    (rankAt : ∀ phase : Fin 8,
      resident[(entry + 1 + 2 * (originalPacket (executionWidth) channels raw).size +
        2 * raw.nodes.size + 11) + phase.val]? =
      (RawAdapterProgram.rankCopyCode (executionWidth)
        (entry + 1 + 2 * (originalPacket (executionWidth) channels raw).size +
          2 * raw.nodes.size + 11) copyEntry)[phase.val]?)
    (copyAt : ∀ phase : Fin (typedCopyColdCode (executionWidth)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length base copyEntry).size,
      resident[copyEntry + phase.val]? =
        (typedCopyColdCode (executionWidth) channels raw.nodes.size
          (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
          raw.roots.length base copyEntry)[phase.val]?)
    (copyCapacity : copyEntry + (typedCopyColdCode (executionWidth)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length base copyEntry).size <
      2 ^ executionWidth),
    ∃ final ticks peak, Execution resident initial final ticks peak ∧
      ticks ≤ 2 * (originalPacket (executionWidth) channels raw).size +
        10 * raw.nodes.size + 321 * numbering.toDAG.countedSize +
        4 * (initial.heap.size + (originalPacket (executionWidth) channels raw).size +
          raw.nodes.size) +
        226 * (numbering.toDAG.roots.map (typedConeIncidenceSize numbering.toDAG)).sum + 207 ∧
      peak ≤ max (initial.liveWords + raw.nodes.size +
          2 * (numberedPacketWords (width := executionWidth) raw valid numbering).length)
        (38 * numbering.toDAG.countedSize + 1884 + suffix.length + initial.output.length) ∧
      final.stack = suffix ∧
      final.output = (numbering.toDAG.roots.map (fun node =>
        boolWord (executionWidth) (numbering.toDAG.eval assignment node))).reverse ++
        initial.output ∧ final.halted = true

attribute [local irreducible] rawExecutionWidth SourceRankCopyContract

private theorem source_width_rank_copy_runtime (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    SourceRankCopyContract raw valid numbering (rawExecutionWidth channels raw) := by
  have atTyped : SourceRankCopyContract raw valid numbering (typedExecutionWidth numbering.toDAG) := by
    unfold SourceRankCopyContract
    exact accepted_rank_copy_runtime_execution raw valid numbering
  exact Eq.mp (congrArg (SourceRankCopyContract raw valid numbering)
    (numbering_execution_width raw valid numbering)) atTyped

def sourceRelocatedCodeAt (resident sourceProgram : Program width 8) (delta : Nat) : Prop :=
  ∀ index : Nat, ∀ inside : index < sourceProgram.size,
    resident[delta + index]? = some
      (RawAdapterProgram.relocatedInstruction delta (sourceProgram[index]'inside))

theorem classified_source_runtime_execution (raw : RawDAG) (valid : raw.WellFormed channels)
    (assignment : Assignment channels)
    (clauses : List (Controller.CNF.Clause (Fin (raw.toUnordered valid).nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses (raw.toUnordered valid))
    (resident : Program (rawExecutionWidth channels raw) 8) (delta conflict : Nat)
    (state : State (rawExecutionWidth channels raw) 8) (suffix : List (Word (rawExecutionWidth channels raw)))
    (emptyHeap : state.heap = #[])
    (input : state.stack = (Controller.Horn.SourceSerialize.heap (width := rawExecutionWidth channels raw) clauses).toList ++ (((originalPacket (rawExecutionWidth channels raw) channels raw).toList) ++
      (List.ofFn (fun channel => boolWord (rawExecutionWidth channels raw) (assignment channel)) ++ suffix)))
    (position : state.pc = word (rawExecutionWidth channels raw) delta) (running : state.halted = false)
    (coldAt : sourceRelocatedCodeAt resident (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses) delta)
    (pushAt : resident[delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size]? = some (.push 7))
    (setupAt : ∀ phase : Fin 9,
      resident[(delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 1) + phase.val]? =
        (Controller.Horn.WorklistSeed.coldSetupCode (n := (raw.toUnordered valid).nodeCount) (rawExecutionWidth channels raw) (Controller.Horn.SourceSerialize.base clauses)
          (Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses)
          (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 10))[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := (raw.toUnordered valid).nodeCount) resident
      (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 10)
      (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57) conflict)
    (capacity : delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57 < 2 ^ (rawExecutionWidth channels raw))
    (heapFits : Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ (rawExecutionWidth channels raw))
    (runtimeAt : ∀ phase : Fin 61,
      resident[(delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57) + phase.val]? =
        (sourceDependencyRuntimeCode (rawExecutionWidth channels raw) (raw.toUnordered valid).nodeCount (Controller.Horn.SourceSerialize.base clauses)
          (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57) conflict)[phase.val]?)
    (runtimeCapacity : delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 118 < 2 ^ (rawExecutionWidth channels raw))
    (accept tag : Nat)
    (cycleAt : ∀ phase : Fin 8,
      resident[(delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 118) + phase.val]? =
        (sourceCycleCode (rawExecutionWidth channels raw)
          (Controller.Horn.WorklistBucketReady.tailSlot (n := (raw.toUnordered valid).nodeCount) (Controller.Horn.SourceSerialize.base clauses))
          (Controller.Horn.WorklistMark.queueStart (n := (raw.toUnordered valid).nodeCount) (Controller.Horn.SourceSerialize.base clauses) + (raw.toUnordered valid).nodeCount)
          accept tag)[phase.val]?)
    (cycleCapacity : delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 126 < 2 ^ (rawExecutionWidth channels raw))
    (rankDone : Nat)
    (rankCapacity : accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 19 < 2 ^ (rawExecutionWidth channels raw))
    (rankRoom : Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum + ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + (raw.toUnordered valid).nodeCount < 2 ^ (rawExecutionWidth channels raw))
    (popAt : resident[accept]? = some (.pop 4))
    (reloadAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident (accept + 1)
      (Controller.Cost.InputLoad.code (width := rawExecutionWidth channels raw) ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length))
    (zeroAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident
      (accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length) (Controller.Cost.Initialize.code (word (rawExecutionWidth channels raw) 0) (raw.toUnordered valid).nodeCount))
    (rankSetupAt : ∀ phase : Fin 11,
      resident[(accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount) + phase.val]? =
        (sourceRankSetupCode (rawExecutionWidth channels raw) (raw.toUnordered valid).nodeCount (Controller.Horn.SourceSerialize.base clauses) ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length
          (accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 11))[phase.val]?)
    (rankAt : ∀ phase : Fin 8,
      resident[(accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 11) + phase.val]? =
        (RawAdapterProgram.rankCopyCode (rawExecutionWidth channels raw) (accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 11) rankDone)[phase.val]?)
    (copyAt : ∀ phase : Fin (typedCopyColdCode (rawExecutionWidth channels raw)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length
        (Controller.Horn.SourceSerialize.base clauses) rankDone).size,
      resident[rankDone + phase.val]? =
        (typedCopyColdCode (rawExecutionWidth channels raw) channels raw.nodes.size
          (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
          raw.roots.length (Controller.Horn.SourceSerialize.base clauses) rankDone)[phase.val]?)
    (copyCapacity : rankDone + (typedCopyColdCode (rawExecutionWidth channels raw)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length
        (Controller.Horn.SourceSerialize.base clauses) rankDone).size <
      2 ^ rawExecutionWidth channels raw)
    (copyRoom : channels + Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses +
        3 * clauses.length + 3 * (clauses.map List.length).sum +
        (originalPacket (rawExecutionWidth channels raw) channels raw).size + raw.nodes.size +
        (5 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
          (rowGuards (originalRows raw)).length + raw.roots.length) < 2 ^ rawExecutionWidth channels raw) :
    ((raw.toUnordered valid).Acyclic ∧
      ∃ numbering : (raw.toUnordered valid).Numbering,
        ∃ final ticks peak, Execution resident state final ticks peak ∧
          ticks ≤ 61 * raw.nodes.size + 115 * (clauses.map List.length).sum + 131 * clauses.length +
            2 * (originalPacket (rawExecutionWidth channels raw) channels raw).size +
            321 * numbering.toDAG.countedSize +
            4 * (Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses +
              3 * clauses.length + 3 * (clauses.map List.length).sum +
              (originalPacket (rawExecutionWidth channels raw) channels raw).size + raw.nodes.size) +
            226 * (numbering.toDAG.roots.map (typedConeIncidenceSize numbering.toDAG)).sum + 305 ∧
          peak ≤ max (state.liveWords + 6 * raw.nodes.size + 6 +
              3 * clauses.length + 3 * (clauses.map List.length).sum +
              2 * (numberedPacketWords (width := rawExecutionWidth channels raw) raw valid numbering).length)
            (38 * numbering.toDAG.countedSize + 1884 + suffix.length + state.output.length) ∧
          final.stack = suffix ∧
          final.output = (numbering.toDAG.roots.map (fun node =>
            boolWord (rawExecutionWidth channels raw) (numbering.toDAG.eval assignment node))).reverse ++
            state.output ∧ final.halted = true) ∨
    (¬(raw.toUnordered valid).Acyclic ∧ ∃ final ticks peak,
      Execution resident state final ticks peak ∧
      ticks ≤ 51 * raw.nodes.size + 115 * (clauses.map List.length).sum + 131 * clauses.length + 98 ∧
      peak ≤ state.liveWords + 5 * raw.nodes.size + 6 +
        3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      final.output = word (rawExecutionWidth channels raw) tag :: state.output ∧ final.halted = true) := by
  let packet := (originalPacket (rawExecutionWidth channels raw) channels raw).toList
  let assignmentWords := List.ofFn (fun channel => boolWord (rawExecutionWidth channels raw)
    (assignment channel))
  obtain ⟨queue, classified, classTicks, classPeak, classTrace, classCost, classSpace,
    stored, ordered, distinct, saved, heapBound, outcome⟩ :=
    RawAdapterProgram.end_saved_classified_execution (raw.toUnordered valid) clauses source
      resident delta conflict state (packet ++ (assignmentWords ++ suffix))
      emptyHeap input position running coldAt pushAt setupAt scanAt capacity heapFits runtimeAt runtimeCapacity
      accept tag cycleAt cycleCapacity
  rcases outcome with accepted | rejected
  · rcases accepted with ⟨acyclic, complete, classPC, classRunning, classOutput⟩
    change queue.length = raw.nodes.size at complete
    let numbering := RawDependencyOrder.numbering (raw.toUnordered valid) queue distinct
      (accepted_queue_complete (raw.toUnordered valid) queue distinct complete) ordered
    have actualQueue : ∀ index : Fin queue.length,
        classified.heap[Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size)
          (Controller.Horn.SourceSerialize.base clauses) + index.val]? =
            some (word (rawExecutionWidth channels raw) queue[index.val].val) := by
      intro index
      have queueFits := stored.queue.fits
      change Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size)
        (Controller.Horn.SourceSerialize.base clauses) + queue.length ≤ classified.heap.size at queueFits
      rw [Array.getElem?_eq_getElem (by have := index.isLt; omega)]
      exact congrArg some (stored.queue.entry index)
    have consumer := source_width_rank_copy_runtime raw valid numbering
    unfold SourceRankCopyContract at consumer
    obtain ⟨final, continuationTicks, continuationPeak, continuationTrace, continuationCost,
      continuationSpace, finalStack, finalOutput, finalHalted⟩ :=
      consumer assignment suffix resident classified (Controller.Horn.SourceSerialize.base clauses)
        accept rankDone classPC classRunning saved stored.fits actualQueue
        (by simp only [packet, Array.length_toList, RawDAG.toUnordered] at rankCapacity; omega)
        (by rw [numbered_packet_length]; omega)
        popAt (by simpa only [Array.length_toList] using reloadAt)
        (by simpa only [Array.length_toList, RawDAG.toUnordered] using zeroAt)
        (by simpa only [Array.length_toList, RawDAG.toUnordered] using rankSetupAt)
        (by simpa only [Array.length_toList, RawDAG.toUnordered] using rankAt) copyAt copyCapacity
    have actualLive : classified.liveWords ≤ classPeak := source_execution_final_live resident classTrace
    have joined := classTrace.append continuationTrace
    refine Or.inl ⟨acyclic, numbering, final, classTicks + continuationTicks,
      max classPeak continuationPeak, joined, ?_, ?_, finalStack,
      finalOutput.trans (by rw [classOutput]), finalHalted⟩
    · have cost : classTicks ≤ 51 * raw.nodes.size + 115 * (clauses.map List.length).sum +
          131 * clauses.length + 98 := by
        simpa only [RawDAG.toUnordered] using classCost
      omega
    · have space : classPeak ≤ state.liveWords + 5 * raw.nodes.size + 6 +
          3 * clauses.length + 3 * (clauses.map List.length).sum := by
        simpa only [RawDAG.toUnordered] using classSpace
      rw [max_le_iff]
      constructor
      · exact le_trans space (le_trans (by omega) (le_max_left _ _))
      · exact le_trans continuationSpace (max_le_max (by omega) (by rw [classOutput]))
  · rcases rejected with ⟨cyclic, rejectedHalted, rejectedOutput⟩
    have cost : classTicks ≤ 51 * raw.nodes.size + 115 * (clauses.map List.length).sum +
        131 * clauses.length + 98 := by
      simpa only [RawDAG.toUnordered] using classCost
    have space : classPeak ≤ state.liveWords + 5 * raw.nodes.size + 6 +
        3 * clauses.length + 3 * (clauses.map List.length).sum := by
      simpa only [RawDAG.toUnordered] using classSpace
    exact Or.inr ⟨cyclic, classified, classTicks, classPeak, classTrace, cost,
      space, rejectedOutput, rejectedHalted⟩

/-- Load the counted packet length and form the actual reverse-save cursor. -/
def originalSaveSetupCode (width sourceBase saveEntry : Nat) : Program width 8 :=
  #[.constant 2 (word width sourceBase),
    .constant 0 (word width (sourceBase + 8)), .load 0 0,
    .add 2 2 0, .constant 7 (word width (2 ^ width - 1)),
    .constant 6 (word width 0), .constant 1 (word width (2 ^ width - 1)),
    .add 1 2 1, .branchZero 6 (word width saveEntry)]

/-- Patch the live arity pointer after saving the unchanged original source. -/
def originalArityPatchCode (width sourceBase : Nat) : Program width 8 :=
  #[.constant 0 (word width sourceBase), .load 2 0,
    .add 2 2 2, .add 2 2 2, .constant 5 (word width 9),
    .add 2 2 5, .constant 5 (word width (sourceBase + 5)), .store 5 2]

/-- Count the appended dependency packet and actual total heap from source fields. -/
def dependencySaveSetupCode (width sourceBase saveEntry : Nat) : Program width 8 :=
  #[.constant 0 (word width sourceBase), .load 0 0,
    .add 0 0 0, .add 0 0 0,
    .constant 1 (word width (sourceBase + 3)), .load 1 1,
    .add 1 1 1, .add 0 0 1,
    .constant 1 (word width 5), .add 0 0 1,
    .constant 2 (word width (sourceBase + 8)), .load 2 2,
    .constant 1 (word width sourceBase), .add 2 2 1,
    .add 2 2 0,
    .constant 7 (word width (2 ^ width - 1)), .constant 6 (word width 0),
    .constant 1 (word width (2 ^ width - 1)), .add 1 2 1,
    .branchZero 6 (word width saveEntry)]


private theorem original_save_setup_execution (resident : Program width 8)
    (entry sourceBase words saveEntry : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 9, resident[entry + phase.val]? =
      (originalSaveSetupCode width sourceBase saveEntry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 9 < 2 ^ width) (headerFits : sourceBase + 8 < 2 ^ width)
    (positive : 0 < words) (endFits : sourceBase + words < 2 ^ width)
    (endCell : state.heap[sourceBase + 8]? = some (word width words)) :
    ∃ final, Execution resident state final 9 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width saveEntry ∧ final.halted = false ∧
      final.reg 0 = word width words ∧ final.reg 1 = word width (sourceBase + words - 1) ∧
      final.reg 2 = word width (sourceBase + words) ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 →
        register ≠ 6 → register ≠ 7 → final.reg register = state.reg register) := by
  let s1 : State width 8 := { state with reg := copyRegisters (state.reg 0) (state.reg 1) (word width sourceBase) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 1), halted := false }
  let s2 : State width 8 := { state with reg := copyRegisters (word width (sourceBase + 8)) (state.reg 1) (word width sourceBase) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 2), halted := false }
  let s3 : State width 8 := { state with reg := copyRegisters (word width words) (state.reg 1) (word width sourceBase) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 3), halted := false }
  let s4 : State width 8 := { state with reg := copyRegisters (word width words) (state.reg 1) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 4), halted := false }
  let s5 : State width 8 := { state with reg := copyRegisters (word width words) (state.reg 1) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (word width (2 ^ width - 1)), pc := word width (entry + 5), halted := false }
  let s6 : State width 8 := { state with reg := copyRegisters (word width words) (state.reg 1) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (word width (2 ^ width - 1)), pc := word width (entry + 6), halted := false }
  let s7 : State width 8 := { state with reg := copyRegisters (word width words) (word width (2 ^ width - 1)) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (word width (2 ^ width - 1)), pc := word width (entry + 7), halted := false }
  let s8 : State width 8 := { state with reg := copyRegisters (word width words) (word width (sourceBase + words - 1)) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (word width (2 ^ width - 1)), pc := word width (entry + 8), halted := false }
  let s9 : State width 8 := { state with reg := copyRegisters (word width words) (word width (sourceBase + words - 1)) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (word width (2 ^ width - 1)), pc := word width (saveEntry), halted := false }
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.constant 2 (word width sourceBase))
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [originalSaveSetupCode] using physical ⟨0, by decide⟩)]
    have result := copy_constant_step state 2 (word width sourceBase) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      fin_cases register <;> simp only [s1, State.advance, State.put, copyRegisters] <;> rfl
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) (by simpa only [Nat.add_zero] using position) (by omega)
    · exact running
  have live1 : s1.liveWords = state.liveWords := rfl
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 0 (word width (sourceBase + 8)))
      (by rfl) (by omega)
      (by simpa [originalSaveSetupCode] using physical ⟨1, by decide⟩)]
    have result := copy_constant_step s1 0 (word width (sourceBase + 8)) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (state.reg 0) (state.reg 1) (word width sourceBase) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (sourceBase + 8))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords := rfl
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.load 0 0)
      (by rfl) (by omega)
      (by simpa [originalSaveSetupCode] using physical ⟨2, by decide⟩)]
    have result := copy_load_step s2 0 0 (sourceBase + 8) (word width words) (by rfl) headerFits (by rfl) endCell
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (sourceBase + 8)) (state.reg 1) (word width sourceBase) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width words)) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords := rfl
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.add 2 2 0)
      (by rfl) (by omega)
      (by simpa [originalSaveSetupCode] using physical ⟨3, by decide⟩)]
    have result := copy_add_step s3 2 2 0 sourceBase words (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width words) (state.reg 1) (word width sourceBase) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (sourceBase + words))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords := rfl
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.constant 7 (word width (2 ^ width - 1)))
      (by rfl) (by omega)
      (by simpa [originalSaveSetupCode] using physical ⟨4, by decide⟩)]
    have result := copy_constant_step s4 7 (word width (2 ^ width - 1)) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update7 (word width words) (state.reg 1) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (2 ^ width - 1))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords := rfl
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.constant 6 (word width 0))
      (by rfl) (by omega)
      (by simpa [originalSaveSetupCode] using physical ⟨5, by decide⟩)]
    have result := copy_constant_step s5 6 (word width 0) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update6 (word width words) (state.reg 1) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (word width (2 ^ width - 1)) (word width 0)) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords := rfl
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 1 (word width (2 ^ width - 1)))
      (by rfl) (by omega)
      (by simpa [originalSaveSetupCode] using physical ⟨6, by decide⟩)]
    have result := copy_constant_step s6 1 (word width (2 ^ width - 1)) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width words) (state.reg 1) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (word width (2 ^ width - 1)) (word width (2 ^ width - 1))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords := rfl
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 1 2 1)
      (by rfl) (by omega)
      (by simpa [originalSaveSetupCode] using physical ⟨7, by decide⟩)]
    have result := copy_add_step s7 1 2 1 (sourceBase + words) (2 ^ width - 1) (by rfl) endFits maskFits (by rfl) (by rfl)
    rw [marker_word_decrement (sourceBase + words) (by omega) endFits] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width words) (word width (2 ^ width - 1)) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (word width 0) (word width (2 ^ width - 1)) (word width (sourceBase + words - 1))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords := rfl
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.branchZero 6 (word width saveEntry))
      (by rfl) (by omega)
      (by simpa [originalSaveSetupCode] using physical ⟨8, by decide⟩)]
    have result := copy_branch_zero s8 6 saveEntry (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live9 : s9.liveWords = state.liveWords := rfl
  have path := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.refl s9)))))))))
  refine ⟨s9, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simpa only [live1, live2, live3, live4, live5, live6, live7, live8, live9, Nat.max_self, Nat.reduceAdd] using path
  · intro register not0 not1 not2 not6 not7
    fin_cases register <;> first | contradiction | rfl

private theorem original_arity_patch_execution (resident : Program width 8)
    (entry sourceBase nodes : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 8, resident[entry + phase.val]? =
      (originalArityPatchCode width sourceBase)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 8 < 2 ^ width) (sourceFits : sourceBase + 5 < 2 ^ width)
    (valueFits : 9 + 4 * nodes < 2 ^ width) (headerBound : sourceBase + 5 < state.heap.size)
    (nodesCell : state.heap[sourceBase]? = some (word width nodes)) :
    ∃ final, Execution resident state final 8 state.liveWords ∧
      final.heap = state.heap.setIfInBounds (sourceBase + 5) (word width (9 + 4 * nodes)) ∧
      final.heap[sourceBase + 5]? = some (word width (9 + 4 * nodes)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 8) ∧ final.halted = false ∧
      (∀ address, address ≠ sourceBase + 5 → final.heap[address]? = state.heap[address]?) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 2 → register ≠ 5 →
        final.reg register = state.reg register) := by
  let s1 : State width 8 := { state with reg := copyRegisters (word width sourceBase) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 1), halted := false }
  let s2 : State width 8 := { state with reg := copyRegisters (word width sourceBase) (state.reg 1) (word width nodes) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 2), halted := false }
  let s3 : State width 8 := { state with reg := copyRegisters (word width sourceBase) (state.reg 1) (word width (nodes + nodes)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 3), halted := false }
  let s4 : State width 8 := { state with reg := copyRegisters (word width sourceBase) (state.reg 1) (word width ((nodes + nodes) + (nodes + nodes))) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 4), halted := false }
  let s5 : State width 8 := { state with reg := copyRegisters (word width sourceBase) (state.reg 1) (word width ((nodes + nodes) + (nodes + nodes))) (state.reg 3) (state.reg 4) (word width 9) (state.reg 6) (state.reg 7), pc := word width (entry + 5), halted := false }
  let s6 : State width 8 := { state with reg := copyRegisters (word width sourceBase) (state.reg 1) (word width (((nodes + nodes) + (nodes + nodes)) + 9)) (state.reg 3) (state.reg 4) (word width 9) (state.reg 6) (state.reg 7), pc := word width (entry + 6), halted := false }
  let s7 : State width 8 := { state with reg := copyRegisters (word width sourceBase) (state.reg 1) (word width (((nodes + nodes) + (nodes + nodes)) + 9)) (state.reg 3) (state.reg 4) (word width (sourceBase + 5)) (state.reg 6) (state.reg 7), pc := word width (entry + 7), halted := false }
  let s8 : State width 8 := { state with reg := copyRegisters (word width sourceBase) (state.reg 1) (word width (((nodes + nodes) + (nodes + nodes)) + 9)) (state.reg 3) (state.reg 4) (word width (sourceBase + 5)) (state.reg 6) (state.reg 7), pc := word width (entry + 8), halted := false, heap := state.heap.setIfInBounds (sourceBase + 5) (word width (9 + 4 * nodes)) }
  have sumEq : ((nodes + nodes) + (nodes + nodes)) + 9 = 9 + 4 * nodes := by omega
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.constant 0 (word width sourceBase))
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [originalArityPatchCode] using physical ⟨0, by decide⟩)]
    have result := copy_constant_step state 0 (word width sourceBase) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      fin_cases register <;> simp only [s1, State.advance, State.put, copyRegisters] <;> rfl
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) (by simpa only [Nat.add_zero] using position) (by omega)
    · exact running
  have live1 : s1.liveWords = state.liveWords := rfl
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.load 2 0)
      (by rfl) (by omega)
      (by simpa [originalArityPatchCode] using physical ⟨1, by decide⟩)]
    have result := copy_load_step s1 2 0 sourceBase (word width nodes) (by rfl) (by omega) (by rfl) nodesCell
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width sourceBase) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width nodes)) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords := rfl
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.add 2 2 2)
      (by rfl) (by omega)
      (by simpa [originalArityPatchCode] using physical ⟨2, by decide⟩)]
    have result := copy_add_step s2 2 2 2 (nodes) (nodes) (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width sourceBase) (state.reg 1) (word width nodes) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (nodes + nodes))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords := rfl
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.add 2 2 2)
      (by rfl) (by omega)
      (by simpa [originalArityPatchCode] using physical ⟨3, by decide⟩)]
    have result := copy_add_step s3 2 2 2 (nodes + nodes) (nodes + nodes) (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width sourceBase) (state.reg 1) (word width (nodes + nodes)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width ((nodes + nodes) + (nodes + nodes)))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords := rfl
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.constant 5 (word width 9))
      (by rfl) (by omega)
      (by simpa [originalArityPatchCode] using physical ⟨4, by decide⟩)]
    have result := copy_constant_step s4 5 (word width 9) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width sourceBase) (state.reg 1) (word width ((nodes + nodes) + (nodes + nodes))) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width 9)) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords := rfl
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.add 2 2 5)
      (by rfl) (by omega)
      (by simpa [originalArityPatchCode] using physical ⟨5, by decide⟩)]
    have result := copy_add_step s5 2 2 5 ((nodes + nodes) + (nodes + nodes)) (9) (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width sourceBase) (state.reg 1) (word width ((nodes + nodes) + (nodes + nodes))) (state.reg 3) (state.reg 4) (word width 9) (state.reg 6) (state.reg 7) (word width (((nodes + nodes) + (nodes + nodes)) + 9))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords := rfl
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.constant 5 (word width (sourceBase + 5)))
      (by rfl) (by omega)
      (by simpa [originalArityPatchCode] using physical ⟨6, by decide⟩)]
    have result := copy_constant_step s6 5 (word width (sourceBase + 5)) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update5 (word width sourceBase) (state.reg 1) (word width (((nodes + nodes) + (nodes + nodes)) + 9)) (state.reg 3) (state.reg 4) (word width 9) (state.reg 6) (state.reg 7) (word width (sourceBase + 5))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords := rfl
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.store 5 2)
      (by rfl) (by omega)
      (by simpa [originalArityPatchCode] using physical ⟨7, by decide⟩)]
    have heldValue : s7.reg 2 = word width (9 + 4 * nodes) := by
      change word width (((nodes + nodes) + (nodes + nodes)) + 9) = word width (9 + 4 * nodes)
      exact congrArg (word width) sumEq
    have result := copy_store_step s7 5 2 (sourceBase + 5) (word width (9 + 4 * nodes))
      (by rfl) headerBound sourceFits (by rfl) heldValue
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords := by simp only [s8, State.liveWords, Array.size_setIfInBounds]
  have path := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.refl s8))))))))
  refine ⟨s8, ?_, rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simpa only [live1, live2, live3, live4, live5, live6, live7, live8, Nat.max_self, Nat.reduceAdd] using path
  · simp only [s8, Array.setIfInBounds_def, dite_eq_left headerBound, Array.getElem?_set headerBound, ite_eq_left rfl, ite_true]
  · intro address different
    simp only [s8, Array.setIfInBounds_def, dite_eq_left headerBound, Array.getElem?_set headerBound, ite_eq_right (Ne.symm different)]
  · intro register not0 not2 not5
    fin_cases register <;> first | contradiction | rfl

private theorem original_packet_end_cell (heap : Array (Word width)) (sourceBase : Nat)
    (raw : RawDAG) (image : OriginalImageStored heap sourceBase channels raw) :
    heap[sourceBase + 8]? = some (word width (originalPacket width channels raw).size) := by
  have scalar : 9 + 6 * (originalRows raw).length + (rowChildren (originalRows raw)).length +
      (rowGuards (originalRows raw)).length + raw.roots.length =
        (originalPacket width channels raw).size := by
    rw [original_packet_size, original_rows_length]
  have cell : heap[sourceBase + 8]? = some (word width
      (9 + 6 * (originalRows raw).length + (rowChildren (originalRows raw)).length +
        (rowGuards (originalRows raw)).length + raw.roots.length)) := by
    apply original_image_cell heap sourceBase channels raw image
    rw [originalPacket, cacheHeap,
      ForestCursorMaterialize.allocatedHeap_prefix width _ _ 8
        (by rw [original_header_size]; decide)]
    simp [originalHeaderHeap, originalHeader, Nat.add_assoc]
  rw [scalar] at cell
  exact cell

/-- Save the unchanged counted original image before patching its live arity
pointer. The packet on the stack is produced by actual reverse-save fetches. -/
private theorem original_source_save_execution (resident : Program width 8)
    (entry saveEntry done sourceBase : Nat) (raw : RawDAG) (state : State width 8)
    (image : OriginalImageStored state.heap sourceBase channels raw)
    (position : state.pc = word width entry) (running : state.halted = false)
    (positiveBase : 0 < sourceBase)
    (sourceFits : sourceBase + (originalPacket width channels raw).size < 2 ^ width)
    (setupFits : entry + 9 < 2 ^ width) (saveFits : saveEntry + 6 < 2 ^ width)
    (setupAt : ∀ phase : Fin 9, resident[entry + phase.val]? =
      (originalSaveSetupCode width sourceBase saveEntry)[phase.val]?)
    (saveAt : RawTransferLoops.CodeAt resident saveEntry
      (RawTransferLoops.reverseSaveCode width saveEntry done)) :
    ∃ final peak, Execution resident state final
        (6 * (originalPacket width channels raw).size + 10) peak ∧
      peak ≤ state.liveWords + (originalPacket width channels raw).size ∧
      final.heap = state.heap ∧
      final.stack = (originalPacket width channels raw).toList ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 2 = word width (sourceBase + (originalPacket width channels raw).size) ∧
      final.reg 6 = word width 0 ∧ final.reg 7 = word width (2 ^ width - 1) := by
  have packetPositive : 0 < (originalPacket width channels raw).size := by
    rw [original_packet_size]
    omega
  have headerFits : sourceBase + 8 < 2 ^ width := by
    have counted := original_packet_size (width := width) channels raw
    omega
  obtain ⟨ready, setupTrace, setupHeap, setupStack, setupOutput, setupPC, setupRunning,
      countReg, cursorReg, endReg, zeroReg, maskReg, setupFrame⟩ :=
    original_save_setup_execution resident entry sourceBase
      (originalPacket width channels raw).size saveEntry state setupAt position running
      setupFits headerFits packetPositive sourceFits
      (original_packet_end_cell state.heap sourceBase raw image)
  have packetCells : ∀ index : Nat, ∀ inside : index < (originalPacket width channels raw).toList.length,
      ready.heap[sourceBase + index]? = some (originalPacket width channels raw).toList[index] := by
    intro index inside
    rw [setupHeap]
    simpa only [Array.length_toList, Array.getElem_toList] using
      image ⟨index, by simpa only [Array.length_toList] using inside⟩
  obtain ⟨final, savePeak, saveTrace, saveSpace, saveHeap, saveStack, saveOutput,
      savePC, saveRunning, finalCount, saveFrame⟩ :=
    RawTransferLoops.reverse_save_execution resident saveEntry done sourceBase
      (originalPacket width channels raw).toList ready setupPC setupRunning saveFits positiveBase
      (by simpa only [Array.length_toList] using sourceFits)
      (by simp only [Array.length_toList]; omega)
      (by simpa only [Array.length_toList] using countReg)
      (by simpa only [Array.length_toList] using cursorReg) maskReg zeroReg packetCells saveAt
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, setupHeap, setupStack, setupOutput]
  refine ⟨final, max state.liveWords savePeak, ?_, ?_, saveHeap.trans setupHeap,
    saveStack.trans (by rw [setupStack]), saveOutput.trans setupOutput, savePC, saveRunning,
    (saveFrame 2 (by decide) (by decide) (by decide)).trans endReg,
    (saveFrame 6 (by decide) (by decide) (by decide)).trans zeroReg,
    (saveFrame 7 (by decide) (by decide) (by decide)).trans maskReg⟩
  · convert setupTrace.append saveTrace using 1 <;> simp only [Array.length_toList] <;> omega
  · simp only [Array.length_toList] at saveSpace
    rw [readyLive] at saveSpace
    omega


/-- The dependency serializer consumes the original ordered child rows, including
all repeated occurrences. Its row list is derived from the original source. -/
private theorem original_dependency_rows (raw : RawDAG)
    (valid : raw.WellFormed channels) :
    (originalRows raw).map Row.children =
      List.ofFn (fun parent : Fin (raw.toUnordered valid).nodeCount =>
        ((raw.toUnordered valid).node parent).children.map Fin.val) := by
  apply List.ext_getElem
  · simp only [List.length_map, original_rows_length, List.length_ofFn] <;> rfl
  · intro position left right
    have bounded : position < (raw.toUnordered valid).nodeCount := by
      simpa only [List.length_ofFn] using right
    let parent : Fin (raw.toUnordered valid).nodeCount := ⟨position, bounded⟩
    have children := (erased_typed_row_matches
      ((raw.toUnordered valid).node parent)).2.2.1
    rw [← original_selected_row raw valid parent] at children
    simpa only [List.getElem_map, List.getElem_ofFn, parent] using children

private theorem original_dependency_arity_vector (raw : RawDAG)
    (valid : raw.WellFormed channels) :
    ((originalRows raw).map Row.children).map List.length =
      List.ofFn (fun parent : Fin (raw.toUnordered valid).nodeCount =>
        ((raw.toUnordered valid).node parent).children.length) := by
  simpa only [List.map_map, Function.comp_def] using
    (original_count_vectors raw valid).1


private theorem dependency_save_setup_execution (resident : Program width 8)
    (entry sourceBase nodes edges words saveEntry : Nat) (state : State width 8)
    (physical : ∀ phase : Fin 20, resident[entry + phase.val]? =
      (dependencySaveSetupCode width sourceBase saveEntry)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 20 < 2 ^ width)
    (headerFits : sourceBase + 8 < 2 ^ width)
    (heapEndFits : sourceBase + words + (5 + 4 * nodes + 2 * edges) < 2 ^ width)
    (nodeCell : state.heap[sourceBase]? = some (word width nodes))
    (edgeCell : state.heap[sourceBase + 3]? = some (word width edges))
    (wordCell : state.heap[sourceBase + 8]? = some (word width words)) :
    ∃ final, Execution resident state final 20 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width saveEntry ∧ final.halted = false ∧
      final.reg 0 = word width (5 + 4 * nodes + 2 * edges) ∧
      final.reg 1 = word width (sourceBase + words + (5 + 4 * nodes + 2 * edges) - 1) ∧
      final.reg 2 = word width (sourceBase + words + (5 + 4 * nodes + 2 * edges)) ∧
      final.reg 6 = word width 0 ∧ final.reg 7 = word width (2 ^ width - 1) ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 1 → register ≠ 2 →
        register ≠ 6 → register ≠ 7 → final.reg register = state.reg register) := by
  let s1 : State width 8 := { state with reg := copyRegisters (word width (sourceBase)) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 1), halted := false }
  let s2 : State width 8 := { state with reg := copyRegisters (word width (nodes)) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 2), halted := false }
  let s3 : State width 8 := { state with reg := copyRegisters (word width (2 * nodes)) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 3), halted := false }
  let s4 : State width 8 := { state with reg := copyRegisters (word width (4 * nodes)) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 4), halted := false }
  let s5 : State width 8 := { state with reg := copyRegisters (word width (4 * nodes)) (word width (sourceBase + 3)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 5), halted := false }
  let s6 : State width 8 := { state with reg := copyRegisters (word width (4 * nodes)) (word width (edges)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 6), halted := false }
  let s7 : State width 8 := { state with reg := copyRegisters (word width (4 * nodes)) (word width (2 * edges)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 7), halted := false }
  let s8 : State width 8 := { state with reg := copyRegisters (word width (4 * nodes + 2 * edges)) (word width (2 * edges)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 8), halted := false }
  let s9 : State width 8 := { state with reg := copyRegisters (word width (4 * nodes + 2 * edges)) (word width (5)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 9), halted := false }
  let s10 : State width 8 := { state with reg := copyRegisters (word width (5 + 4 * nodes + 2 * edges)) (word width (5)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 10), halted := false }
  let s11 : State width 8 := { state with reg := copyRegisters (word width (5 + 4 * nodes + 2 * edges)) (word width (5)) (word width (sourceBase + 8)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 11), halted := false }
  let s12 : State width 8 := { state with reg := copyRegisters (word width (5 + 4 * nodes + 2 * edges)) (word width (5)) (word width (words)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 12), halted := false }
  let s13 : State width 8 := { state with reg := copyRegisters (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase)) (word width (words)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 13), halted := false }
  let s14 : State width 8 := { state with reg := copyRegisters (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase)) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 14), halted := false }
  let s15 : State width 8 := { state with reg := copyRegisters (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges))) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7), pc := word width (entry + 15), halted := false }
  let s16 : State width 8 := { state with reg := copyRegisters (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges))) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (word width (2 ^ width - 1)), pc := word width (entry + 16), halted := false }
  let s17 : State width 8 := { state with reg := copyRegisters (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges))) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 17), halted := false }
  let s18 : State width 8 := { state with reg := copyRegisters (word width (5 + 4 * nodes + 2 * edges)) (word width (2 ^ width - 1)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges))) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 18), halted := false }
  let s19 : State width 8 := { state with reg := copyRegisters (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges) - 1)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges))) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (entry + 19), halted := false }
  let s20 : State width 8 := { state with reg := copyRegisters (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges) - 1)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges))) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), pc := word width (saveEntry), halted := false }
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.constant 0 (word width (sourceBase)))
      (by simpa only [Nat.add_zero] using position) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨0, by decide⟩)]
    have result := copy_constant_step state 0 (word width (sourceBase)) running
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      fin_cases register <;> simp only [s1, State.advance, State.put, copyRegisters] <;> rfl
    · rfl
    · rfl
    · rfl
    · change state.advance.pc = word width (entry + 1)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state
        (entry + 0) (by simpa only [Nat.add_zero] using position) (by omega)
    · exact running
  have live1 : s1.liveWords = state.liveWords := rfl
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.load 0 0)
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨1, by decide⟩)]
    have result := copy_load_step s1 0 0 (sourceBase) (word width (nodes)) (by rfl) (by omega) (by rfl) nodeCell
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (sourceBase)) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (nodes))) register
    · rfl
    · rfl
    · rfl
    · change s1.advance.pc = word width (entry + 2)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1
        (entry + 1) (by rfl) (by omega)
    · rfl
  have live2 : s2.liveWords = state.liveWords := rfl
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.add 0 0 0)
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨2, by decide⟩)]
    have result := copy_add_step s2 0 0 0 (nodes) (nodes) (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    have sumEq : (nodes) + (nodes) = 2 * nodes := by omega
    rw [sumEq] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (nodes)) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (2 * nodes))) register
    · rfl
    · rfl
    · rfl
    · change s2.advance.pc = word width (entry + 3)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2
        (entry + 2) (by rfl) (by omega)
    · rfl
  have live3 : s3.liveWords = state.liveWords := rfl
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.add 0 0 0)
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨3, by decide⟩)]
    have result := copy_add_step s3 0 0 0 (2 * nodes) (2 * nodes) (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    have sumEq : (2 * nodes) + (2 * nodes) = 4 * nodes := by omega
    rw [sumEq] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (2 * nodes)) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (4 * nodes))) register
    · rfl
    · rfl
    · rfl
    · change s3.advance.pc = word width (entry + 4)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3
        (entry + 3) (by rfl) (by omega)
    · rfl
  have live4 : s4.liveWords = state.liveWords := rfl
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.constant 1 (word width (sourceBase + 3)))
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨4, by decide⟩)]
    have result := copy_constant_step s4 1 (word width (sourceBase + 3)) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (4 * nodes)) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (sourceBase + 3))) register
    · rfl
    · rfl
    · rfl
    · change s4.advance.pc = word width (entry + 5)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4
        (entry + 4) (by rfl) (by omega)
    · rfl
  have live5 : s5.liveWords = state.liveWords := rfl
  have t5 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.load 1 1)
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨5, by decide⟩)]
    have result := copy_load_step s5 1 1 (sourceBase + 3) (word width (edges)) (by rfl) (by omega) (by rfl) edgeCell
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (4 * nodes)) (word width (sourceBase + 3)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (edges))) register
    · rfl
    · rfl
    · rfl
    · change s5.advance.pc = word width (entry + 6)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5
        (entry + 5) (by rfl) (by omega)
    · rfl
  have live6 : s6.liveWords = state.liveWords := rfl
  have t6 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.add 1 1 1)
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨6, by decide⟩)]
    have result := copy_add_step s6 1 1 1 (edges) (edges) (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    have sumEq : (edges) + (edges) = 2 * edges := by omega
    rw [sumEq] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (4 * nodes)) (word width (edges)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (2 * edges))) register
    · rfl
    · rfl
    · rfl
    · change s6.advance.pc = word width (entry + 7)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6
        (entry + 6) (by rfl) (by omega)
    · rfl
  have live7 : s7.liveWords = state.liveWords := rfl
  have t7 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 0 0 1)
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨7, by decide⟩)]
    have result := copy_add_step s7 0 0 1 (4 * nodes) (2 * edges) (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    have sumEq : (4 * nodes) + (2 * edges) = 4 * nodes + 2 * edges := by omega
    rw [sumEq] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (4 * nodes)) (word width (2 * edges)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (4 * nodes + 2 * edges))) register
    · rfl
    · rfl
    · rfl
    · change s7.advance.pc = word width (entry + 8)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7
        (entry + 7) (by rfl) (by omega)
    · rfl
  have live8 : s8.liveWords = state.liveWords := rfl
  have t8 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.constant 1 (word width (5)))
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨8, by decide⟩)]
    have result := copy_constant_step s8 1 (word width (5)) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (4 * nodes + 2 * edges)) (word width (2 * edges)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (5))) register
    · rfl
    · rfl
    · rfl
    · change s8.advance.pc = word width (entry + 9)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8
        (entry + 8) (by rfl) (by omega)
    · rfl
  have live9 : s9.liveWords = state.liveWords := rfl
  have t9 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.add 0 0 1)
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨9, by decide⟩)]
    have result := copy_add_step s9 0 0 1 (4 * nodes + 2 * edges) (5) (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    have sumEq : (4 * nodes + 2 * edges) + (5) = 5 + 4 * nodes + 2 * edges := by omega
    rw [sumEq] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update0 (word width (4 * nodes + 2 * edges)) (word width (5)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (5 + 4 * nodes + 2 * edges))) register
    · rfl
    · rfl
    · rfl
    · change s9.advance.pc = word width (entry + 10)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9
        (entry + 9) (by rfl) (by omega)
    · rfl
  have live10 : s10.liveWords = state.liveWords := rfl
  have t10 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.constant 2 (word width (sourceBase + 8)))
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨10, by decide⟩)]
    have result := copy_constant_step s10 2 (word width (sourceBase + 8)) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (5 + 4 * nodes + 2 * edges)) (word width (5)) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (sourceBase + 8))) register
    · rfl
    · rfl
    · rfl
    · change s10.advance.pc = word width (entry + 11)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s10
        (entry + 10) (by rfl) (by omega)
    · rfl
  have live11 : s11.liveWords = state.liveWords := rfl
  have t11 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.load 2 2)
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨11, by decide⟩)]
    have result := copy_load_step s11 2 2 (sourceBase + 8) (word width (words)) (by rfl) (by omega) (by rfl) wordCell
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (5 + 4 * nodes + 2 * edges)) (word width (5)) (word width (sourceBase + 8)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (words))) register
    · rfl
    · rfl
    · rfl
    · change s11.advance.pc = word width (entry + 12)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s11
        (entry + 11) (by rfl) (by omega)
    · rfl
  have live12 : s12.liveWords = state.liveWords := rfl
  have t12 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.constant 1 (word width (sourceBase)))
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨12, by decide⟩)]
    have result := copy_constant_step s12 1 (word width (sourceBase)) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (5 + 4 * nodes + 2 * edges)) (word width (5)) (word width (words)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (sourceBase))) register
    · rfl
    · rfl
    · rfl
    · change s12.advance.pc = word width (entry + 13)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s12
        (entry + 12) (by rfl) (by omega)
    · rfl
  have live13 : s13.liveWords = state.liveWords := rfl
  have t13 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.add 2 2 1)
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨13, by decide⟩)]
    have result := copy_add_step s13 2 2 1 (words) (sourceBase) (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    have sumEq : (words) + (sourceBase) = sourceBase + words := by omega
    rw [sumEq] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase)) (word width (words)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (sourceBase + words))) register
    · rfl
    · rfl
    · rfl
    · change s13.advance.pc = word width (entry + 14)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s13
        (entry + 13) (by rfl) (by omega)
    · rfl
  have live14 : s14.liveWords = state.liveWords := rfl
  have t14 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 14) (.add 2 2 0)
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨14, by decide⟩)]
    have result := copy_add_step s14 2 2 0 (sourceBase + words) (5 + 4 * nodes + 2 * edges) (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    have sumEq : (sourceBase + words) + (5 + 4 * nodes + 2 * edges) = sourceBase + words + (5 + 4 * nodes + 2 * edges) := by omega
    rw [sumEq] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update2 (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase)) (word width (sourceBase + words)) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges)))) register
    · rfl
    · rfl
    · rfl
    · change s14.advance.pc = word width (entry + 15)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s14
        (entry + 14) (by rfl) (by omega)
    · rfl
  have live15 : s15.liveWords = state.liveWords := rfl
  have t15 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 15) (.constant 7 (word width (2 ^ width - 1)))
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨15, by decide⟩)]
    have result := copy_constant_step s15 7 (word width (2 ^ width - 1)) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update7 (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges))) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (state.reg 7) (word width (2 ^ width - 1))) register
    · rfl
    · rfl
    · rfl
    · change s15.advance.pc = word width (entry + 16)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s15
        (entry + 15) (by rfl) (by omega)
    · rfl
  have live16 : s16.liveWords = state.liveWords := rfl
  have t16 : programStep resident s16 = some s17 := by
    rw [fetched resident s16 (entry + 16) (.constant 6 (word width (0)))
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨16, by decide⟩)]
    have result := copy_constant_step s16 6 (word width (0)) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update6 (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges))) (state.reg 3) (state.reg 4) (state.reg 5) (state.reg 6) (word width (2 ^ width - 1)) (word width (0))) register
    · rfl
    · rfl
    · rfl
    · change s16.advance.pc = word width (entry + 17)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s16
        (entry + 16) (by rfl) (by omega)
    · rfl
  have live17 : s17.liveWords = state.liveWords := rfl
  have t17 : programStep resident s17 = some s18 := by
    rw [fetched resident s17 (entry + 17) (.constant 1 (word width (2 ^ width - 1)))
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨17, by decide⟩)]
    have result := copy_constant_step s17 1 (word width (2 ^ width - 1)) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (5 + 4 * nodes + 2 * edges)) (word width (sourceBase)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges))) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (2 ^ width - 1))) register
    · rfl
    · rfl
    · rfl
    · change s17.advance.pc = word width (entry + 18)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s17
        (entry + 17) (by rfl) (by omega)
    · rfl
  have live18 : s18.liveWords = state.liveWords := rfl
  have t18 : programStep resident s18 = some s19 := by
    rw [fetched resident s18 (entry + 18) (.add 1 2 1)
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨18, by decide⟩)]
    have result := copy_add_step s18 1 2 1 (sourceBase + words + (5 + 4 * nodes + 2 * edges)) (2 ^ width - 1) (by rfl) (by omega) (by omega) (by rfl) (by rfl)
    rw [marker_word_decrement (sourceBase + words + (5 + 4 * nodes + 2 * edges)) (by omega) heapEndFits] at result
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      exact congrFun (copyRegisters_update1 (word width (5 + 4 * nodes + 2 * edges)) (word width (2 ^ width - 1)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges))) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)) (word width (sourceBase + words + (5 + 4 * nodes + 2 * edges) - 1))) register
    · rfl
    · rfl
    · rfl
    · change s18.advance.pc = word width (entry + 19)
      simpa only [Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s18
        (entry + 18) (by rfl) (by omega)
    · rfl
  have live19 : s19.liveWords = state.liveWords := rfl
  have t19 : programStep resident s19 = some s20 := by
    rw [fetched resident s19 (entry + 19) (.branchZero 6 (word width saveEntry))
      (by rfl) (by omega)
      (by simpa [dependencySaveSetupCode] using physical ⟨19, by decide⟩)]
    have result := copy_branch_zero s19 6 saveEntry (by rfl) (by rfl)
    refine result.trans (congrArg some ?_)
    apply copy_state_ext
    · intro register
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have live20 : s20.liveWords = state.liveWords := rfl
  have path := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.cons t16 (Execution.cons t17 (Execution.cons t18 (Execution.cons t19 (Execution.refl s20))))))))))))))))))))
  refine ⟨s20, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · simpa only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live11, live12, live13, live14, live15, live16, live17, live18, live19, live20, Nat.max_self, Nat.reduceAdd] using path
  · intro register not0 not1 not2 not6 not7
    fin_cases register <;> first | contradiction | rfl

private theorem original_child_row_total (rows : List Row) :
    ((rows.map Row.children).map List.length).sum = (rowChildren rows).length := by
  simp only [rowChildren, List.length_flatMap, List.map_map, Function.comp_def]

/-- The live arity-header patch and dependency serialization form one fetched
trace over the saved original source. No dependency row table is supplied. -/
private theorem original_dependency_serializer_execution (resident : Program width 8)
    (entry sourceBase : Nat) (raw : RawDAG) (valid : raw.WellFormed channels)
    (state : State width 8)
    (image : OriginalImageStored state.heap sourceBase channels raw)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 64 < 2 ^ width)
    (sourceFits : sourceBase + (originalPacket width channels raw).size < 2 ^ width)
    (packetFits : 5 + 4 * raw.nodes.size +
      2 * (rowChildren (originalRows raw)).length < 2 ^ width)
    (room : state.heap.size + 5 + 4 * raw.nodes.size +
      2 * (rowChildren (originalRows raw)).length ≤ 2 ^ width)
    (patchAt : ∀ phase : Fin 8, resident[entry + phase.val]? =
      (originalArityPatchCode width sourceBase)[phase.val]?)
    (serializerAt : ∀ phase : Fin 56, resident[(entry + 8) + phase.val]? =
      (RawAdapterProgram.dependencySerializerCode width (entry + 8) sourceBase)[phase.val]?) :
    ∃ final peak, Execution resident state final
        (22 * raw.nodes.size + 7 * (rowChildren (originalRows raw)).length + 38) peak ∧
      peak ≤ state.liveWords + 6 + 4 * raw.nodes.size +
        2 * (rowChildren (originalRows raw)).length ∧
      final.heap = state.heap.setIfInBounds (sourceBase + 5)
        (word width (9 + 4 * raw.nodes.size)) ++
        Controller.Horn.SourceSerialize.heap (width := width)
          (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 64) ∧ final.halted = false := by
  let rows := (originalRows raw).map Row.children
  have rowsLength : rows.length = raw.nodes.size := by
    simp only [rows, List.length_map, original_rows_length]
  have childrenTotal : (rows.map List.length).sum =
      (rowChildren (originalRows raw)).length := original_child_row_total _
  have packetSize := original_packet_size (width := width) channels raw
  have globals := original_global_cells raw state.heap sourceBase channels image
  have headerBound : sourceBase + 5 < state.heap.size := by
    have inside : 5 < (originalPacket width channels raw).size := by rw [packetSize]; omega
    have stored := image ⟨5, inside⟩
    obtain ⟨bound, cell⟩ := Array.getElem?_eq_some_iff.mp stored
    omega
  obtain ⟨patched, patchTrace, patchedHeap, arityCell, patchStack, patchOutput,
      patchPC, patchRunning, patchFrame, patchRegisters⟩ :=
    original_arity_patch_execution resident entry sourceBase raw.nodes.size state
      patchAt position running (by omega) (by omega) (by omega) headerBound globals.1
  have patchedSize : patched.heap.size = state.heap.size := by
    rw [patchedHeap, Array.size_setIfInBounds]
  have patchedLive : patched.liveWords = state.liveWords := by
    simp only [State.liveWords, patchedSize, patchStack, patchOutput]
  have rowCell : patched.heap[sourceBase]? = some (word width rows.length) := by
    rw [patchFrame sourceBase (by omega), rowsLength]
    exact globals.1
  obtain ⟨rowBound, rowValue⟩ := Array.getElem?_eq_some_iff.mp rowCell
  obtain ⟨arityBound, arityValue⟩ := Array.getElem?_eq_some_iff.mp arityCell
  have arities : ∀ index : Fin rows.length,
      patched.heap[(sourceBase + 9 + 4 * rows.length) + 2 * index.val]? =
        some (word width rows[index].length) := by
    intro index
    have inside : index.val < (originalRows raw).length := by
      simpa only [rows, List.length_map] using index.isLt
    have cell := (original_arity_cells state.heap sourceBase channels raw image index.val inside).1
    rw [patchFrame _ (by omega)]
    simpa only [rowsLength, rows, Fin.getElem_fin, List.getElem_map, Nat.add_assoc] using cell
  have children : ∀ index : Fin rows.length, ∀ child : Fin rows[index].length,
      patched.heap[(sourceBase + 9 + 6 * rows.length) +
        ((rows.take index.val).map List.length).sum + child.val]? =
        some (word width rows[index][child]) := by
    intro index child
    have inside : index.val < (originalRows raw).length := by
      simpa only [rows, List.length_map] using index.isLt
    have childInside : child.val < ((originalRows raw)[index.val]).children.length := by
      simpa only [rows, Fin.getElem_fin, List.getElem_map] using child.isLt
    have cell := original_child_cell state.heap sourceBase channels raw image
      index.val inside child.val childInside
    have takeTotal : ((rows.take index.val).map List.length).sum =
        (rowChildren ((originalRows raw).take index.val)).length := by
      rw [show rows.take index.val = ((originalRows raw).take index.val).map Row.children
        by simp only [rows, List.map_take]]
      exact original_child_row_total _
    rw [patchFrame _ (by omega), takeTotal]
    simpa only [rowsLength, rows, Fin.getElem_fin, List.getElem_map, Nat.add_assoc] using cell
  obtain ⟨final, serializePeak, serializeTrace, serializeSpace, serializeHeap,
      serializeStack, serializeOutput, serializePC, serializeRunning⟩ :=
    RawAdapterProgram.dependency_serializer_execution resident (entry + 8) sourceBase rows patched
      serializerAt (by omega)
      (by change sourceBase + 9 + 6 * rows.length + (rows.map List.length).sum < _
          rw [rowsLength, childrenTotal]; omega)
      (by change 5 + 4 * rows.length + 2 * (rows.map List.length).sum < _
          rw [rowsLength, childrenTotal]; exact packetFits)
      (by change patched.heap.size + 5 + 4 * rows.length +
            2 * (rows.map List.length).sum ≤ _
          rw [patchedSize, rowsLength, childrenTotal]; exact room)
      rowBound arityBound
      rowValue
      (by simpa only [rowsLength] using arityValue)
      arities children patchPC patchRunning
  have exactPacket := RawAdapterProgram.dependency_packet_exact
    (width := width) (raw.toUnordered valid)
  rw [← original_dependency_rows raw valid,
    ← original_dependency_arity_vector raw valid] at exactPacket
  have finalHeap : final.heap = state.heap.setIfInBounds (sourceBase + 5)
      (word width (9 + 4 * raw.nodes.size)) ++
      Controller.Horn.SourceSerialize.heap (width := width)
        (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)) := by
    rw [serializeHeap, patchedHeap]
    congr 1
    simpa only [rows, List.length_map, original_rows_length, RawDAG.toUnordered] using exactPacket
  refine ⟨final, max state.liveWords serializePeak, ?_, ?_, finalHeap,
    serializeStack.trans patchStack, serializeOutput.trans patchOutput,
    ?_, serializeRunning⟩
  · have joined := patchTrace.append serializeTrace
    change Execution resident state final
      (8 + (22 * rows.length + 7 * (rows.map List.length).sum + 30)) _ at joined
    convert joined using 1 <;> rw [rowsLength, childrenTotal] <;> omega
  · change serializePeak ≤ patched.liveWords + 6 + 4 * rows.length +
      2 * (rows.map List.length).sum at serializeSpace
    rw [patchedLive, rowsLength, childrenTotal] at serializeSpace
    omega
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using serializePC

/-- Save the exact original counted packet, patch only its live arity header,
and serialize its ordered dependency occurrences by fetched instructions. -/
theorem saved_original_dependency_execution (resident : Program width 8)
    (entry sourceBase : Nat) (raw : RawDAG) (valid : raw.WellFormed channels)
    (state : State width 8)
    (image : OriginalImageStored state.heap sourceBase channels raw)
    (position : state.pc = word width entry) (running : state.halted = false)
    (positiveBase : 0 < sourceBase)
    (codeFits : entry + 79 < 2 ^ width)
    (sourceFits : sourceBase + (originalPacket width channels raw).size < 2 ^ width)
    (packetFits : 5 + 4 * raw.nodes.size +
      2 * (rowChildren (originalRows raw)).length < 2 ^ width)
    (room : state.heap.size + 5 + 4 * raw.nodes.size +
      2 * (rowChildren (originalRows raw)).length ≤ 2 ^ width)
    (setupAt : ∀ phase : Fin 9, resident[entry + phase.val]? =
      (originalSaveSetupCode width sourceBase (entry + 9))[phase.val]?)
    (saveAt : RawTransferLoops.CodeAt resident (entry + 9)
      (RawTransferLoops.reverseSaveCode width (entry + 9) (entry + 15)))
    (patchAt : ∀ phase : Fin 8, resident[(entry + 15) + phase.val]? =
      (originalArityPatchCode width sourceBase)[phase.val]?)
    (serializerAt : ∀ phase : Fin 56, resident[(entry + 23) + phase.val]? =
      (RawAdapterProgram.dependencySerializerCode width (entry + 23) sourceBase)[phase.val]?) :
    ∃ final peak, Execution resident state final
        (6 * (originalPacket width channels raw).size + 22 * raw.nodes.size +
          7 * (rowChildren (originalRows raw)).length + 48) peak ∧
      peak ≤ state.liveWords + (originalPacket width channels raw).size +
        6 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length ∧
      final.heap = state.heap.setIfInBounds (sourceBase + 5)
        (word width (9 + 4 * raw.nodes.size)) ++
        Controller.Horn.SourceSerialize.heap (width := width)
          (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)) ∧
      final.stack = (originalPacket width channels raw).toList ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 79) ∧
      final.halted = false := by
  obtain ⟨saved, savePeak, saveTrace, saveSpace, saveHeap, saveStack, saveOutput,
      savePC, saveRunning, savedEnd, savedZero, savedMask⟩ :=
    original_source_save_execution resident entry (entry + 9) (entry + 15)
      sourceBase raw state image position running positiveBase sourceFits
      (by omega) (by omega) setupAt saveAt
  have savedImage : OriginalImageStored saved.heap sourceBase channels raw := by
    rw [saveHeap]
    exact image
  have savedLive : saved.liveWords = state.liveWords +
      (originalPacket width channels raw).size := by
    simp only [State.liveWords, saveHeap, saveStack, saveOutput,
      List.length_append, Array.length_toList]
    omega
  obtain ⟨final, serializePeak, serializeTrace, serializeSpace, serializeHeap,
      serializeStack, serializeOutput, serializePC, serializeRunning⟩ :=
    original_dependency_serializer_execution resident (entry + 15) sourceBase raw valid saved
      savedImage savePC saveRunning (by omega) sourceFits packetFits
      (by rw [saveHeap]; exact room) patchAt
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using serializerAt)
  refine ⟨final, max savePeak serializePeak, ?_, ?_, ?_,
    serializeStack.trans saveStack, serializeOutput.trans saveOutput,
    ?_, serializeRunning⟩
  · convert saveTrace.append serializeTrace using 1 <;> omega
  · rw [savedLive] at serializeSpace
    omega
  · simpa only [saveHeap] using serializeHeap
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using serializePC

private theorem dependency_parent_length_sum (rows : List (List Nat)) :
    (rows.map (fun children => children.length + 1)).sum =
      (rows.map List.length).sum + rows.length := by
  induction rows with
  | nil => rfl
  | cons children rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

theorem original_dependency_packet_size (raw : RawDAG)
    (valid : raw.WellFormed channels) :
    (Controller.Horn.SourceSerialize.heap (width := width)
      (RawDependencyOrder.dependencyClauses (raw.toUnordered valid))).size =
      5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length := by
  let rows := (originalRows raw).map Row.children
  have rowCount : rows.length = raw.nodes.size := by
    simp only [rows, List.length_map, original_rows_length]
  have clauseCount : (RawDependencyOrder.dependencyClauses
      (raw.toUnordered valid)).length = raw.nodes.size := by
    simp only [RawDependencyOrder.dependencyClauses, List.length_ofFn, RawDAG.toUnordered]
  have lengths : (RawDependencyOrder.dependencyClauses
      (raw.toUnordered valid)).map List.length =
        rows.map (fun children => children.length + 1) := by
    rw [show rows = List.ofFn (fun parent : Fin (raw.toUnordered valid).nodeCount =>
      ((raw.toUnordered valid).node parent).children.map Fin.val)
      from original_dependency_rows raw valid]
    simp only [RawDependencyOrder.dependencyClauses, RawDependencyOrder.dependencyClause,
      List.map_ofFn, List.length_cons, List.length_map, Function.comp_def, Nat.add_comm]
  have total : (rows.map List.length).sum =
      (rowChildren (originalRows raw)).length := original_child_row_total _
  rw [Controller.Horn.SourceSerialize.heap_size, Controller.Horn.SourceSerialize.base,
    Controller.Horn.SourceSerialize.source, clauseCount, lengths,
    dependency_parent_length_sum, total, rowCount]
  omega

def dependencyReleaseSetupCode (width releaseEntry : Nat) : Program width 8 :=
  #[.add 0 2 6, .branchZero 6 (word width releaseEntry)]

private theorem dependency_release_setup_execution (resident : Program width 8)
    (entry releaseEntry count : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 2 < 2 ^ width) (countFits : count < 2 ^ width)
    (countHeld : state.reg 2 = word width count) (zeroHeld : state.reg 6 = word width 0)
    (physical : ∀ phase : Fin 2, resident[entry + phase.val]? =
      (dependencyReleaseSetupCode width releaseEntry)[phase.val]?) :
    ∃ final, Execution resident state final 2 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width releaseEntry ∧ final.halted = false ∧
      final.reg 0 = word width count ∧
      (∀ register : Fin 8, register ≠ 0 → final.reg register = state.reg register) := by
  let middle := state.advance.put 0 (word width count)
  let final := { middle.advance with pc := word width releaseEntry }
  have t0 : programStep resident state = some middle := by
    rw [fetched resident state entry (.add 0 2 6) position (by omega)
      (by simpa [dependencyReleaseSetupCode] using physical ⟨0, by decide⟩)]
    simpa only [Nat.add_zero] using
      copy_add_step state 0 2 6 count 0 running countFits (Nat.two_pow_pos width)
        countHeld zeroHeld
  have middlePC : middle.pc = word width (entry + 1) := by
    change state.advance.pc = _
    exact referenceAdvancePC state entry position (by omega)
  have middleRunning : middle.halted = false := running
  have middleZero : middle.reg 6 = word width 0 := by
    simpa only [middle, State.advance, State.put, ite_eq_right (by decide : (6 : Fin 8) ≠ 0)] using zeroHeld
  have t1 : programStep resident middle = some final := by
    rw [fetched resident middle (entry + 1) (.branchZero 6 (word width releaseEntry))
      middlePC (by omega)
      (by simpa [dependencyReleaseSetupCode] using physical ⟨1, by decide⟩)]
    exact copy_branch_zero middle 6 releaseEntry middleRunning middleZero
  have middleLive : middle.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running, ?_, ?_⟩
  · simpa only [middleLive, finalLive, Nat.max_self, Nat.reduceAdd] using
      Execution.cons t0 (Execution.cons t1 (Execution.refl final))
  · simp only [final, middle, State.advance, State.put, ite_true]
  · intro register different
    simp only [final, middle, State.advance, State.put, ite_eq_right different]

private theorem dependency_cold_handoff_execution (resident : Program width 8)
    (entry coldEntry : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (entryFits : entry < 2 ^ width) (zeroHeld : state.reg 6 = word width 0)
    (physical : resident[entry]? = some (.branchZero 6 (word width coldEntry))) :
    ∃ final, Execution resident state final 1 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width coldEntry ∧ final.halted = false := by
  let final := { state.advance with pc := word width coldEntry }
  have transition : programStep resident state = some final := by
    rw [fetched resident state entry (.branchZero 6 (word width coldEntry))
      position entryFits physical]
    exact copy_branch_zero state 6 coldEntry running zeroHeld
  have finalLive : final.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, rfl, rfl, rfl, rfl, running⟩
  simpa only [finalLive, Nat.max_self, Nat.reduceAdd] using
    Execution.cons transition (Execution.refl final)

private theorem dependency_save_trace_join (resident : Program width 8)
    (entry done base : Nat) (packet : Array (Word width)) (state ready : State width 8)
    (setupTrace : Execution resident state ready 20 state.liveWords)
    (readyHeap : ready.heap = state.heap) (readyStack : ready.stack = state.stack)
    (readyOutput : ready.output = state.output)
    (position : ready.pc = word width entry) (running : ready.halted = false)
    (codeFits : entry + 6 < 2 ^ width) (positive : 0 < base)
    (heapFits : base + packet.size < 2 ^ width)
    (count : ready.reg 0 = word width packet.size)
    (cursor : ready.reg 1 = word width (base + packet.size - 1))
    (endHeld : ready.reg 2 = word width state.heap.size)
    (mask : ready.reg 7 = word width (2 ^ width - 1)) (zero : ready.reg 6 = word width 0)
    (cells : ∀ index : Nat, ∀ inside : index < packet.toList.length,
      ready.heap[base + index]? = some packet.toList[index])
    (codeAt : RawTransferLoops.CodeAt resident entry (RawTransferLoops.reverseSaveCode width entry done)) :
    ∃ final peak, Execution resident state final (6 * packet.size + 21) peak ∧
      peak ≤ state.liveWords + packet.size ∧ final.heap = state.heap ∧
      final.stack = packet.toList ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.reg 2 = word width state.heap.size ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) := by
  obtain ⟨final, savePeak, trace, space, heap, stack, output, pc, halted, finalCount, frame⟩ :=
    RawTransferLoops.reverse_save_execution resident entry done base packet.toList ready
      position running codeFits positive
      (by simpa only [Array.length_toList] using heapFits)
      (by simp only [Array.length_toList]; omega)
      (by simpa only [Array.length_toList] using count)
      (by simpa only [Array.length_toList] using cursor) mask zero cells codeAt
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, readyHeap, readyStack, readyOutput]
  refine ⟨final, max state.liveWords savePeak, ?_, ?_, heap.trans readyHeap,
    stack.trans (by rw [readyStack]), output.trans readyOutput, pc, halted,
    (frame 2 (by decide) (by decide) (by decide)).trans endHeld,
    (frame 6 (by decide) (by decide) (by decide)).trans zero,
    (frame 7 (by decide) (by decide) (by decide)).trans mask⟩
  · convert setupTrace.append trace using 1 <;> simp only [Array.length_toList] <;> omega
  · simp only [Array.length_toList] at space
    rw [readyLive] at space
    omega

private theorem generated_dependency_save_execution (resident : Program width 8)
    (entry saveEntry done sourceBase : Nat) (raw : RawDAG)
    (valid : raw.WellFormed channels) (original : Array (Word width))
    (state : State width 8)
    (packet : state.heap = original ++ Controller.Horn.SourceSerialize.heap
      (width := width) (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)))
    (originalSize : original.size = sourceBase + (originalPacket width channels raw).size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 20 < 2 ^ width) (saveFits : saveEntry + 6 < 2 ^ width)
    (heapFits : sourceBase + (originalPacket width channels raw).size +
      (5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length) < 2 ^ width)
    (nodeCell : state.heap[sourceBase]? = some (word width raw.nodes.size))
    (edgeCell : state.heap[sourceBase + 3]? =
      some (word width (rowChildren (originalRows raw)).length))
    (wordCell : state.heap[sourceBase + 8]? =
      some (word width (originalPacket width channels raw).size))
    (setupAt : ∀ phase : Fin 20, resident[entry + phase.val]? =
      (dependencySaveSetupCode width sourceBase saveEntry)[phase.val]?)
    (saveAt : RawTransferLoops.CodeAt resident saveEntry
      (RawTransferLoops.reverseSaveCode width saveEntry done)) :
    ∃ final peak, Execution resident state final
        (6 * (Controller.Horn.SourceSerialize.heap (width := width)
          (RawDependencyOrder.dependencyClauses (raw.toUnordered valid))).size + 21) peak ∧
      peak ≤ state.liveWords + (Controller.Horn.SourceSerialize.heap (width := width)
        (RawDependencyOrder.dependencyClauses (raw.toUnordered valid))).size ∧
      final.heap = state.heap ∧
      final.stack = (Controller.Horn.SourceSerialize.heap (width := width)
        (RawDependencyOrder.dependencyClauses (raw.toUnordered valid))).toList ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 2 = word width state.heap.size ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) := by
  let dependencyPacket := Controller.Horn.SourceSerialize.heap (width := width)
    (RawDependencyOrder.dependencyClauses (raw.toUnordered valid))
  have dependencySize : dependencyPacket.size =
      5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length :=
    original_dependency_packet_size raw valid
  have originalPacketSize := original_packet_size (width := width) channels raw
  have totalSize : state.heap.size = sourceBase + (originalPacket width channels raw).size +
      dependencyPacket.size := by
    rw [packet, Array.size_append, originalSize]
  obtain ⟨ready, setupTrace, readyHeap, readyStack, readyOutput, readyPC, readyRunning,
      readyCount, readyCursor, readyEnd, readyZero, readyMask, readyFrame⟩ :=
    dependency_save_setup_execution resident entry sourceBase raw.nodes.size
      (rowChildren (originalRows raw)).length (originalPacket width channels raw).size
      saveEntry state setupAt position running codeFits (by omega) heapFits
      nodeCell edgeCell wordCell
  have cells : ∀ index : Nat, ∀ inside : index < dependencyPacket.toList.length,
      ready.heap[sourceBase + (originalPacket width channels raw).size + index]? =
        some dependencyPacket.toList[index] := by
    intro index inside
    rw [readyHeap, packet]
    have indexFits : index < dependencyPacket.size := by
      simpa only [Array.length_toList] using inside
    rw [← originalSize, Array.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left, Array.getElem_toList]
    change dependencyPacket[index]? = some dependencyPacket[index]
    exact Array.getElem?_eq_getElem indexFits
  have readyCount' : ready.reg 0 = word width dependencyPacket.size := by
    simpa only [dependencySize] using readyCount
  have readyCursor' : ready.reg 1 = word width
      (sourceBase + (originalPacket width channels raw).size + dependencyPacket.size - 1) := by
    simpa only [dependencySize] using readyCursor
  have readyEnd' : ready.reg 2 = word width state.heap.size := by
    rw [totalSize, dependencySize]
    exact readyEnd
  have joined := dependency_save_trace_join resident saveEntry done
    (sourceBase + (originalPacket width channels raw).size) dependencyPacket state ready
    setupTrace readyHeap readyStack readyOutput readyPC readyRunning saveFits (by omega)
    (by simpa only [dependencySize] using heapFits) readyCount' readyCursor' readyEnd'
    readyMask readyZero cells saveAt
  exact joined

/-- Fixed-base caller prefix after the charged parser reloads one original
packet and retains its identical saved image on the stack. -/
def sourceZeroTransferCode (width entry coldEntry : Nat) : Program width 8 :=
  originalArityPatchCode width 0 ++
    RawAdapterProgram.dependencySerializerCode width (entry + 8) 0 ++
    dependencySaveSetupCode width 0 (entry + 84) ++
    RawTransferLoops.reverseSaveCode width (entry + 84) (entry + 90) ++
    dependencyReleaseSetupCode width (entry + 92) ++
    RawTransferLoops.countedReleaseCode width (entry + 92) (entry + 96) ++
    #[.branchZero 6 (word width coldEntry)]

/-- Serialize and transfer the dependency packet from the actual original image
at address zero, then enter the classifier with no heap or stack reset. -/
private theorem source_zero_transfer_execution (resident : Program width 8)
    (entry coldEntry : Nat) (raw : RawDAG) (valid : raw.WellFormed channels)
    (state : State width 8)
    (image : OriginalImageStored state.heap 0 channels raw)
    (originalSize : state.heap.size = (originalPacket width channels raw).size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 97 < 2 ^ width)
    (heapFits : (originalPacket width channels raw).size + 5 + 4 * raw.nodes.size +
      2 * (rowChildren (originalRows raw)).length < 2 ^ width)
    (patchAt : ∀ phase : Fin 8, resident[entry + phase.val]? =
      (originalArityPatchCode width 0)[phase.val]?)
    (serializerAt : ∀ phase : Fin 56, resident[(entry + 8) + phase.val]? =
      (RawAdapterProgram.dependencySerializerCode width (entry + 8) 0)[phase.val]?)
    (saveSetupAt : ∀ phase : Fin 20, resident[(entry + 64) + phase.val]? =
      (dependencySaveSetupCode width 0 (entry + 84))[phase.val]?)
    (saveAt : RawTransferLoops.CodeAt resident (entry + 84)
      (RawTransferLoops.reverseSaveCode width (entry + 84) (entry + 90)))
    (releaseSetupAt : ∀ phase : Fin 2, resident[(entry + 90) + phase.val]? =
      (dependencyReleaseSetupCode width (entry + 92))[phase.val]?)
    (releaseAt : RawTransferLoops.CodeAt resident (entry + 92)
      (RawTransferLoops.countedReleaseCode width (entry + 92) (entry + 96)))
    (handoffAt : resident[entry + 96]? = some (.branchZero 6 (word width coldEntry))) :
    ∃ final peak, Execution resident state final
        (22 * raw.nodes.size + 7 * (rowChildren (originalRows raw)).length +
          6 * (5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length) +
          4 * ((originalPacket width channels raw).size + 5 + 4 * raw.nodes.size +
            2 * (rowChildren (originalRows raw)).length) + 63) peak ∧
      peak ≤ state.liveWords +
        2 * (5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length) ∧
      final.heap = #[] ∧
      final.stack = (Controller.Horn.SourceSerialize.heap (width := width)
        (RawDependencyOrder.dependencyClauses (raw.toUnordered valid))).toList ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width coldEntry ∧ final.halted = false := by
  let dependencyPacket := Controller.Horn.SourceSerialize.heap (width := width)
    (RawDependencyOrder.dependencyClauses (raw.toUnordered valid))
  let original := state.heap.setIfInBounds 5 (word width (9 + 4 * raw.nodes.size))
  have dependencySize : dependencyPacket.size =
      5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length :=
    original_dependency_packet_size raw valid
  have packetSize := original_packet_size (width := width) channels raw
  have oldSize : original.size = (originalPacket width channels raw).size := by
    simp only [original, Array.size_setIfInBounds, originalSize]
  have headerBound : 5 < state.heap.size := by rw [originalSize, packetSize]; omega
  have preserve : ∀ address value, address ≠ 5 → state.heap[address]? = some value →
      original[address]? = some value := by
    intro address value different cell
    simpa only [original, Array.setIfInBounds_def, dite_eq_left headerBound,
      Array.getElem?_set headerBound, ite_eq_right (Ne.symm different)] using cell
  obtain ⟨serialized, serializePeak, serializeTrace, serializeSpace, serializeHeap,
      serializeStack, serializeOutput, serializePC, serializeRunning⟩ :=
    original_dependency_serializer_execution resident entry 0 raw valid state image
      position running (by omega) (by omega) (by omega)
      (by rw [originalSize]; omega) patchAt serializerAt
  have serializedHeap : serialized.heap = original ++ dependencyPacket := by
    simpa only [Nat.zero_add] using serializeHeap
  have globals := original_global_cells raw state.heap 0 channels image
  have countCell : serialized.heap[0]? = some (word width raw.nodes.size) :=
    source_rank_appended_cell original serialized.heap dependencyPacket serializedHeap 0 _
      (preserve 0 _ (by decide) (by simpa only [Nat.zero_add] using globals.1))
  have edgeCell : serialized.heap[3]? = some
      (word width (rowChildren (originalRows raw)).length) :=
    source_rank_appended_cell original serialized.heap dependencyPacket serializedHeap 3 _
      (preserve 3 _ (by decide) (by simpa only [Nat.zero_add] using globals.2.2.2.1))
  have endCell : serialized.heap[8]? = some (word width (originalPacket width channels raw).size) :=
    source_rank_appended_cell original serialized.heap dependencyPacket serializedHeap 8 _
      (preserve 8 _ (by decide)
        (by simpa only [Nat.zero_add] using original_packet_end_cell state.heap 0 raw image))
  obtain ⟨saved, savePeak, saveTrace, saveSpace, saveHeap, saveStack, saveOutput,
      savePC, saveRunning, savedCount, savedZero, savedMask⟩ :=
    generated_dependency_save_execution resident (entry + 64) (entry + 84) (entry + 90)
      0 raw valid original serialized serializedHeap (by simpa only [Nat.zero_add] using oldSize)
      serializePC serializeRunning (by omega) (by omega)
      (by simpa only [Nat.zero_add, Nat.add_assoc] using heapFits)
      countCell edgeCell endCell saveSetupAt saveAt
  change Execution resident serialized saved (6 * dependencyPacket.size + 21) savePeak at saveTrace
  change savePeak ≤ serialized.liveWords + dependencyPacket.size at saveSpace
  have totalSize : saved.heap.size = (originalPacket width channels raw).size + dependencyPacket.size := by
    rw [saveHeap, serializedHeap, Array.size_append, oldSize]
  have countHeld : saved.reg 2 = word width saved.heap.size := by
    simpa only [saveHeap] using savedCount
  have totalFits : saved.heap.size < 2 ^ width := by
    rw [totalSize, dependencySize]
    simpa only [Nat.add_assoc] using heapFits
  obtain ⟨releaseReady, releaseSetupTrace, readyHeap, readyStack, readyOutput,
      readyPC, readyRunning, readyCount, readyRegisters⟩ :=
    dependency_release_setup_execution resident (entry + 90) (entry + 92)
      saved.heap.size saved savePC saveRunning (by omega) totalFits countHeld savedZero releaseSetupAt
  obtain ⟨released, releasePeak, releaseTrace, releaseSpace, releasedHeap, releasedStack,
      releasedOutput, releasedPC, releasedRunning, releasedCount, releasedRegisters⟩ :=
    RawTransferLoops.counted_release_execution resident (entry + 92) (entry + 96)
      saved.heap.size releaseReady readyPC readyRunning (by omega)
      (congrArg Array.size readyHeap) totalFits readyCount
      ((readyRegisters 7 (by decide)).trans savedMask)
      ((readyRegisters 6 (by decide)).trans savedZero) releaseAt
  obtain ⟨final, handoffTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning⟩ :=
    dependency_cold_handoff_execution resident (entry + 96) coldEntry released
      releasedPC releasedRunning (by omega)
      ((releasedRegisters 6 (by decide)).trans
        ((readyRegisters 6 (by decide)).trans savedZero)) handoffAt
  have serializedLive : serialized.liveWords = state.liveWords + dependencyPacket.size := by
    simp only [State.liveWords, serializedHeap, Array.size_append, oldSize,
      serializeStack, serializeOutput]
    rw [originalSize]
    omega
  have saveIncrement : saved.liveWords = serialized.liveWords + dependencyPacket.size := by
    simp only [State.liveWords, saveHeap, saveStack, saveOutput,
      List.length_append, Array.length_toList, dependencyPacket]
    omega
  have savedLive : saved.liveWords = state.liveWords + 2 * dependencyPacket.size := by
    rw [saveIncrement, serializedLive]
    omega
  have readyLive : releaseReady.liveWords = saved.liveWords := by
    simp only [State.liveWords, readyHeap, readyStack, readyOutput]
  have releasedLive : released.liveWords ≤ saved.liveWords := by
    simp only [State.liveWords, releasedHeap, releasedStack, releasedOutput,
      readyStack, readyOutput, Array.size_empty]
    omega
  let peak := max (max (max (max serializePeak savePeak) saved.liveWords) releasePeak) released.liveWords
  refine ⟨final, peak, ?_, ?_, finalHeap.trans releasedHeap,
    finalStack.trans (releasedStack.trans (readyStack.trans
      (saveStack.trans (by rw [serializeStack])))),
    finalOutput.trans (releasedOutput.trans (readyOutput.trans
      (saveOutput.trans serializeOutput))), finalPC, finalRunning⟩
  · have trace := (((serializeTrace.append saveTrace).append releaseSetupTrace).append
      releaseTrace).append handoffTrace
    convert trace using 1 <;> (try simp only [totalSize, dependencySize]) <;> omega
  · rw [serializedLive] at saveSpace
    rw [readyLive] at releaseSpace
    rw [dependencySize] at savedLive saveSpace
    dsimp only [peak]
    omega


def dependencyPacketLength (raw : RawDAG) : Nat :=
  5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length

def sourceTransferTicks (width channels : Nat) (raw : RawDAG) : Nat :=
  22 * raw.nodes.size + 7 * (rowChildren (originalRows raw)).length +
    6 * dependencyPacketLength raw +
    4 * ((originalPacket width channels raw).size + dependencyPacketLength raw) + 63

/-- The actual original-source serializer and fixed transfers enter the checked
classifier, derived numbering, rank copy and typed evaluator on the same state. -/
theorem source_zero_runtime_execution (raw : RawDAG) (valid : raw.WellFormed channels)
    (assignment : Assignment channels)
    (clauses : List (Controller.CNF.Clause (Fin (raw.toUnordered valid).nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses (raw.toUnordered valid))
    (resident : Program (rawExecutionWidth channels raw) 8) (delta conflict : Nat)
    (state : State (rawExecutionWidth channels raw) 8) (suffix : List (Word (rawExecutionWidth channels raw)))
    (entry : Nat)
    (image : OriginalImageStored state.heap 0 channels raw)
    (originalSize : state.heap.size = (originalPacket (rawExecutionWidth channels raw) channels raw).size)
    (input : state.stack = (originalPacket (rawExecutionWidth channels raw) channels raw).toList ++
      (List.ofFn (fun channel => boolWord (rawExecutionWidth channels raw) (assignment channel)) ++ suffix))
    (position : state.pc = word (rawExecutionWidth channels raw) entry) (running : state.halted = false)
    (transferFits : entry + 97 < 2 ^ rawExecutionWidth channels raw)
    (transferHeapFits : (originalPacket (rawExecutionWidth channels raw) channels raw).size +
      5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length <
      2 ^ rawExecutionWidth channels raw)
    (patchAt : ∀ phase : Fin 8, resident[entry + phase.val]? =
      (originalArityPatchCode (rawExecutionWidth channels raw) 0)[phase.val]?)
    (serializerAt : ∀ phase : Fin 56, resident[(entry + 8) + phase.val]? =
      (RawAdapterProgram.dependencySerializerCode (rawExecutionWidth channels raw) (entry + 8) 0)[phase.val]?)
    (saveSetupAt : ∀ phase : Fin 20, resident[(entry + 64) + phase.val]? =
      (dependencySaveSetupCode (rawExecutionWidth channels raw) 0 (entry + 84))[phase.val]?)
    (saveAt : RawTransferLoops.CodeAt resident (entry + 84)
      (RawTransferLoops.reverseSaveCode (rawExecutionWidth channels raw) (entry + 84) (entry + 90)))
    (releaseSetupAt : ∀ phase : Fin 2, resident[(entry + 90) + phase.val]? =
      (dependencyReleaseSetupCode (rawExecutionWidth channels raw) (entry + 92))[phase.val]?)
    (releaseAt : RawTransferLoops.CodeAt resident (entry + 92)
      (RawTransferLoops.countedReleaseCode (rawExecutionWidth channels raw) (entry + 92) (entry + 96)))
    (handoffAt : resident[entry + 96]? = some (.branchZero 6 (word (rawExecutionWidth channels raw) delta)))
    (coldAt : sourceRelocatedCodeAt resident (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses) delta)
    (pushAt : resident[delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size]? = some (.push 7))
    (setupAt : ∀ phase : Fin 9,
      resident[(delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 1) + phase.val]? =
        (Controller.Horn.WorklistSeed.coldSetupCode (n := (raw.toUnordered valid).nodeCount) (rawExecutionWidth channels raw) (Controller.Horn.SourceSerialize.base clauses)
          (Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses)
          (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 10))[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := (raw.toUnordered valid).nodeCount) resident
      (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 10)
      (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57) conflict)
    (capacity : delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57 < 2 ^ (rawExecutionWidth channels raw))
    (heapFits : Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ (rawExecutionWidth channels raw))
    (runtimeAt : ∀ phase : Fin 61,
      resident[(delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57) + phase.val]? =
        (sourceDependencyRuntimeCode (rawExecutionWidth channels raw) (raw.toUnordered valid).nodeCount (Controller.Horn.SourceSerialize.base clauses)
          (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57) conflict)[phase.val]?)
    (runtimeCapacity : delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 118 < 2 ^ (rawExecutionWidth channels raw))
    (accept tag : Nat)
    (cycleAt : ∀ phase : Fin 8,
      resident[(delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 118) + phase.val]? =
        (sourceCycleCode (rawExecutionWidth channels raw)
          (Controller.Horn.WorklistBucketReady.tailSlot (n := (raw.toUnordered valid).nodeCount) (Controller.Horn.SourceSerialize.base clauses))
          (Controller.Horn.WorklistMark.queueStart (n := (raw.toUnordered valid).nodeCount) (Controller.Horn.SourceSerialize.base clauses) + (raw.toUnordered valid).nodeCount)
          accept tag)[phase.val]?)
    (cycleCapacity : delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 126 < 2 ^ (rawExecutionWidth channels raw))
    (rankDone : Nat)
    (rankCapacity : accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 19 < 2 ^ (rawExecutionWidth channels raw))
    (rankRoom : Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum + ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + (raw.toUnordered valid).nodeCount < 2 ^ (rawExecutionWidth channels raw))
    (popAt : resident[accept]? = some (.pop 4))
    (reloadAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident (accept + 1)
      (Controller.Cost.InputLoad.code (width := rawExecutionWidth channels raw) ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length))
    (zeroAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident
      (accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length) (Controller.Cost.Initialize.code (word (rawExecutionWidth channels raw) 0) (raw.toUnordered valid).nodeCount))
    (rankSetupAt : ∀ phase : Fin 11,
      resident[(accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount) + phase.val]? =
        (sourceRankSetupCode (rawExecutionWidth channels raw) (raw.toUnordered valid).nodeCount (Controller.Horn.SourceSerialize.base clauses) ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length
          (accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 11))[phase.val]?)
    (rankAt : ∀ phase : Fin 8,
      resident[(accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 11) + phase.val]? =
        (RawAdapterProgram.rankCopyCode (rawExecutionWidth channels raw) (accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 11) rankDone)[phase.val]?)
    (copyAt : ∀ phase : Fin (typedCopyColdCode (rawExecutionWidth channels raw)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length
        (Controller.Horn.SourceSerialize.base clauses) rankDone).size,
      resident[rankDone + phase.val]? =
        (typedCopyColdCode (rawExecutionWidth channels raw) channels raw.nodes.size
          (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
          raw.roots.length (Controller.Horn.SourceSerialize.base clauses) rankDone)[phase.val]?)
    (copyCapacity : rankDone + (typedCopyColdCode (rawExecutionWidth channels raw)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length
        (Controller.Horn.SourceSerialize.base clauses) rankDone).size <
      2 ^ rawExecutionWidth channels raw)
    (copyRoom : channels + Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses +
        3 * clauses.length + 3 * (clauses.map List.length).sum +
        (originalPacket (rawExecutionWidth channels raw) channels raw).size + raw.nodes.size +
        (5 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
          (rowGuards (originalRows raw)).length + raw.roots.length) < 2 ^ rawExecutionWidth channels raw) :
    ((raw.toUnordered valid).Acyclic ∧
      ∃ numbering : (raw.toUnordered valid).Numbering,
        ∃ final ticks peak, Execution resident state final ticks peak ∧
          ticks ≤ sourceTransferTicks (rawExecutionWidth channels raw) channels raw + 61 * raw.nodes.size + 115 * (clauses.map List.length).sum + 131 * clauses.length +
            2 * (originalPacket (rawExecutionWidth channels raw) channels raw).size +
            321 * numbering.toDAG.countedSize +
            4 * (Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses +
              3 * clauses.length + 3 * (clauses.map List.length).sum +
              (originalPacket (rawExecutionWidth channels raw) channels raw).size + raw.nodes.size) +
            226 * (numbering.toDAG.roots.map (typedConeIncidenceSize numbering.toDAG)).sum + 305 ∧
          peak ≤ max (state.liveWords + 3 * dependencyPacketLength raw + 6 * raw.nodes.size + 6 +
              3 * clauses.length + 3 * (clauses.map List.length).sum +
              2 * (numberedPacketWords (width := rawExecutionWidth channels raw) raw valid numbering).length)
            (38 * numbering.toDAG.countedSize + 1884 + suffix.length + state.output.length) ∧
          final.stack = suffix ∧
          final.output = (numbering.toDAG.roots.map (fun node =>
            boolWord (rawExecutionWidth channels raw) (numbering.toDAG.eval assignment node))).reverse ++
            state.output ∧ final.halted = true) ∨
    (¬(raw.toUnordered valid).Acyclic ∧ ∃ final ticks peak,
      Execution resident state final ticks peak ∧
      ticks ≤ sourceTransferTicks (rawExecutionWidth channels raw) channels raw + 51 * raw.nodes.size + 115 * (clauses.map List.length).sum + 131 * clauses.length + 98 ∧
      peak ≤ state.liveWords + 3 * dependencyPacketLength raw + 5 * raw.nodes.size + 6 +
        3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      final.output = word (rawExecutionWidth channels raw) tag :: state.output ∧ final.halted = true) := by

  obtain ⟨handoff, transferPeak, transferTrace, transferSpace, handoffHeap, handoffStack,
      handoffOutput, handoffPC, handoffRunning⟩ :=
    source_zero_transfer_execution resident entry delta raw valid state image originalSize
      position running transferFits transferHeapFits patchAt serializerAt saveSetupAt saveAt
      releaseSetupAt releaseAt handoffAt
  have packetSize : (Controller.Horn.SourceSerialize.heap
      (width := rawExecutionWidth channels raw) clauses).size = dependencyPacketLength raw := by
    rw [source]
    exact original_dependency_packet_size raw valid
  have transferredInput : handoff.stack = (Controller.Horn.SourceSerialize.heap
      (width := rawExecutionWidth channels raw) clauses).toList ++
      ((originalPacket (rawExecutionWidth channels raw) channels raw).toList ++
        (List.ofFn (fun channel => boolWord (rawExecutionWidth channels raw) (assignment channel)) ++ suffix)) := by
    rw [handoffStack, input, source]
  have handoffLive : handoff.liveWords ≤ state.liveWords + dependencyPacketLength raw := by
    have packetSize' := original_dependency_packet_size (width := rawExecutionWidth channels raw) raw valid
    simp only [State.liveWords, handoffHeap, handoffStack, handoffOutput,
      Array.size_empty, List.length_append, Array.length_toList, packetSize', dependencyPacketLength]
    omega
  have transferTime : sourceTransferTicks (rawExecutionWidth channels raw) channels raw =
      22 * raw.nodes.size + 7 * (rowChildren (originalRows raw)).length +
        6 * (5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length) +
        4 * ((originalPacket (rawExecutionWidth channels raw) channels raw).size + 5 +
          4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length) + 63 := by
    simp only [sourceTransferTicks, dependencyPacketLength, Nat.add_assoc]
  have continuation := classified_source_runtime_execution raw valid assignment clauses source
    resident delta conflict handoff suffix handoffHeap transferredInput handoffPC handoffRunning
    coldAt pushAt setupAt scanAt capacity heapFits runtimeAt runtimeCapacity accept tag cycleAt
    cycleCapacity rankDone rankCapacity rankRoom popAt reloadAt zeroAt rankSetupAt rankAt copyAt
    copyCapacity copyRoom
  rcases continuation with accepted | rejected
  · rcases accepted with ⟨acyclic, numbering, final, ticks, peak, runtimeTrace, runtimeCost,
      runtimeSpace, finalStack, finalOutput, finalHalted⟩
    refine Or.inl ⟨acyclic, numbering, final,
      sourceTransferTicks (rawExecutionWidth channels raw) channels raw + ticks,
      max transferPeak peak, ?_, ?_, ?_, finalStack, ?_, finalHalted⟩
    · simpa only [transferTime] using transferTrace.append runtimeTrace
    · omega
    · rw [max_le_iff]
      constructor
      · exact le_trans transferSpace (le_trans (by
          dsimp only [dependencyPacketLength] at *
          omega) (le_max_left _ _))
      · exact le_trans runtimeSpace (max_le_max (by
          dsimp only [dependencyPacketLength] at *
          omega) (by rw [handoffOutput]))
    · simpa only [handoffOutput] using finalOutput
  · rcases rejected with ⟨cyclic, final, ticks, peak, runtimeTrace, runtimeCost,
      runtimeSpace, finalOutput, finalHalted⟩
    refine Or.inr ⟨cyclic, final,
      sourceTransferTicks (rawExecutionWidth channels raw) channels raw + ticks,
      max transferPeak peak, ?_, ?_, ?_, ?_, finalHalted⟩
    · simpa only [transferTime] using transferTrace.append runtimeTrace
    · omega
    · dsimp only [dependencyPacketLength] at *
      omega
    · simpa only [handoffOutput] using finalOutput

private theorem source_zero_patch_size (width : Nat) :
    (originalArityPatchCode width 0).size = 8 := rfl
private theorem source_zero_setup_size (width entry : Nat) :
    (dependencySaveSetupCode width 0 entry).size = 20 := rfl
private theorem source_zero_release_setup_size (width entry : Nat) :
    (dependencyReleaseSetupCode width entry).size = 2 := rfl

theorem source_zero_code_size (width entry coldEntry : Nat) :
    (sourceZeroTransferCode width entry coldEntry).size = 97 := by
  have patchSize : (originalArityPatchCode width 0).size = 8 := rfl
  have setupSize : (dependencySaveSetupCode width 0 (entry + 84)).size = 20 := rfl
  have releaseSetupSize : (dependencyReleaseSetupCode width (entry + 92)).size = 2 := rfl
  simp only [sourceZeroTransferCode, Array.size_append, patchSize, setupSize,
    releaseSetupSize, RawAdapterProgram.dependencySerializerCode_size,
    RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size,
    List.length_cons, List.length_nil] <;> rfl

private theorem source_zero_patch_part (resident : Program width 8) (entry coldEntry : Nat)
    (physical : ∀ phase : Fin (sourceZeroTransferCode width entry coldEntry).size,
      resident[entry + phase.val]? = (sourceZeroTransferCode width entry coldEntry)[phase.val]?) :
    ∀ phase : Fin 8, resident[(entry + 0) + phase.val]? =
      (originalArityPatchCode width 0)[phase.val]? := by
  let before : Program width 8 := #[]
  let fragment : Program width 8 := originalArityPatchCode width 0
  let after : Program width 8 := (RawAdapterProgram.dependencySerializerCode width (entry + 8) 0) ++ (dependencySaveSetupCode width 0 (entry + 84)) ++ (RawTransferLoops.reverseSaveCode width (entry + 84) (entry + 90)) ++ (dependencyReleaseSetupCode width (entry + 92)) ++ (RawTransferLoops.countedReleaseCode width (entry + 92) (entry + 96)) ++ (#[.branchZero 6 (word width coldEntry)])
  have layout : sourceZeroTransferCode width entry coldEntry = (before ++ fragment) ++ after := by
    simp only [sourceZeroTransferCode, before, fragment, after, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 0 := by
    rfl
  have fragmentSize : fragment.size = 8 := by
    rfl
  exact extract_copy_section resident (sourceZeroTransferCode width entry coldEntry)
    before fragment after entry 0 8 layout beforeSize fragmentSize physical

private theorem source_zero_serialize_part (resident : Program width 8) (entry coldEntry : Nat)
    (physical : ∀ phase : Fin (sourceZeroTransferCode width entry coldEntry).size,
      resident[entry + phase.val]? = (sourceZeroTransferCode width entry coldEntry)[phase.val]?) :
    ∀ phase : Fin 56, resident[(entry + 8) + phase.val]? =
      (RawAdapterProgram.dependencySerializerCode width (entry + 8) 0)[phase.val]? := by
  let before : Program width 8 := (originalArityPatchCode width 0)
  let fragment : Program width 8 := RawAdapterProgram.dependencySerializerCode width (entry + 8) 0
  let after : Program width 8 := (dependencySaveSetupCode width 0 (entry + 84)) ++ (RawTransferLoops.reverseSaveCode width (entry + 84) (entry + 90)) ++ (dependencyReleaseSetupCode width (entry + 92)) ++ (RawTransferLoops.countedReleaseCode width (entry + 92) (entry + 96)) ++ (#[.branchZero 6 (word width coldEntry)])
  have layout : sourceZeroTransferCode width entry coldEntry = (before ++ fragment) ++ after := by
    simp only [sourceZeroTransferCode, before, fragment, after, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 8 := by
    simp only [before, Array.size_append, source_zero_patch_size, source_zero_setup_size,
      source_zero_release_setup_size, RawAdapterProgram.dependencySerializerCode_size,
      RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size]
  have fragmentSize : fragment.size = 56 := by
    simp only [fragment, RawAdapterProgram.dependencySerializerCode_size,
      RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size]
  exact extract_copy_section resident (sourceZeroTransferCode width entry coldEntry)
    before fragment after entry 8 56 layout beforeSize fragmentSize physical

private theorem source_zero_setup_part (resident : Program width 8) (entry coldEntry : Nat)
    (physical : ∀ phase : Fin (sourceZeroTransferCode width entry coldEntry).size,
      resident[entry + phase.val]? = (sourceZeroTransferCode width entry coldEntry)[phase.val]?) :
    ∀ phase : Fin 20, resident[(entry + 64) + phase.val]? =
      (dependencySaveSetupCode width 0 (entry + 84))[phase.val]? := by
  let before : Program width 8 := (originalArityPatchCode width 0) ++ (RawAdapterProgram.dependencySerializerCode width (entry + 8) 0)
  let fragment : Program width 8 := dependencySaveSetupCode width 0 (entry + 84)
  let after : Program width 8 := (RawTransferLoops.reverseSaveCode width (entry + 84) (entry + 90)) ++ (dependencyReleaseSetupCode width (entry + 92)) ++ (RawTransferLoops.countedReleaseCode width (entry + 92) (entry + 96)) ++ (#[.branchZero 6 (word width coldEntry)])
  have layout : sourceZeroTransferCode width entry coldEntry = (before ++ fragment) ++ after := by
    simp only [sourceZeroTransferCode, before, fragment, after, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 64 := by
    simp only [before, Array.size_append, source_zero_patch_size, source_zero_setup_size,
      source_zero_release_setup_size, RawAdapterProgram.dependencySerializerCode_size,
      RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size]
  have fragmentSize : fragment.size = 20 := by
    rfl
  exact extract_copy_section resident (sourceZeroTransferCode width entry coldEntry)
    before fragment after entry 64 20 layout beforeSize fragmentSize physical

private theorem source_zero_save_part (resident : Program width 8) (entry coldEntry : Nat)
    (physical : ∀ phase : Fin (sourceZeroTransferCode width entry coldEntry).size,
      resident[entry + phase.val]? = (sourceZeroTransferCode width entry coldEntry)[phase.val]?) :
    ∀ phase : Fin 6, resident[(entry + 84) + phase.val]? =
      (RawTransferLoops.reverseSaveCode width (entry + 84) (entry + 90))[phase.val]? := by
  let before : Program width 8 := (originalArityPatchCode width 0) ++ (RawAdapterProgram.dependencySerializerCode width (entry + 8) 0) ++ (dependencySaveSetupCode width 0 (entry + 84))
  let fragment : Program width 8 := RawTransferLoops.reverseSaveCode width (entry + 84) (entry + 90)
  let after : Program width 8 := (dependencyReleaseSetupCode width (entry + 92)) ++ (RawTransferLoops.countedReleaseCode width (entry + 92) (entry + 96)) ++ (#[.branchZero 6 (word width coldEntry)])
  have layout : sourceZeroTransferCode width entry coldEntry = (before ++ fragment) ++ after := by
    simp only [sourceZeroTransferCode, before, fragment, after, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 84 := by
    simp only [before, Array.size_append, source_zero_patch_size, source_zero_setup_size,
      source_zero_release_setup_size, RawAdapterProgram.dependencySerializerCode_size,
      RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size]
  have fragmentSize : fragment.size = 6 := by
    simp only [fragment, RawAdapterProgram.dependencySerializerCode_size,
      RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size]
  exact extract_copy_section resident (sourceZeroTransferCode width entry coldEntry)
    before fragment after entry 84 6 layout beforeSize fragmentSize physical

private theorem source_zero_releaseSetup_part (resident : Program width 8) (entry coldEntry : Nat)
    (physical : ∀ phase : Fin (sourceZeroTransferCode width entry coldEntry).size,
      resident[entry + phase.val]? = (sourceZeroTransferCode width entry coldEntry)[phase.val]?) :
    ∀ phase : Fin 2, resident[(entry + 90) + phase.val]? =
      (dependencyReleaseSetupCode width (entry + 92))[phase.val]? := by
  let before : Program width 8 := (originalArityPatchCode width 0) ++ (RawAdapterProgram.dependencySerializerCode width (entry + 8) 0) ++ (dependencySaveSetupCode width 0 (entry + 84)) ++ (RawTransferLoops.reverseSaveCode width (entry + 84) (entry + 90))
  let fragment : Program width 8 := dependencyReleaseSetupCode width (entry + 92)
  let after : Program width 8 := (RawTransferLoops.countedReleaseCode width (entry + 92) (entry + 96)) ++ (#[.branchZero 6 (word width coldEntry)])
  have layout : sourceZeroTransferCode width entry coldEntry = (before ++ fragment) ++ after := by
    simp only [sourceZeroTransferCode, before, fragment, after, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 90 := by
    simp only [before, Array.size_append, source_zero_patch_size, source_zero_setup_size,
      source_zero_release_setup_size, RawAdapterProgram.dependencySerializerCode_size,
      RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size]
  have fragmentSize : fragment.size = 2 := by
    rfl
  exact extract_copy_section resident (sourceZeroTransferCode width entry coldEntry)
    before fragment after entry 90 2 layout beforeSize fragmentSize physical

private theorem source_zero_release_part (resident : Program width 8) (entry coldEntry : Nat)
    (physical : ∀ phase : Fin (sourceZeroTransferCode width entry coldEntry).size,
      resident[entry + phase.val]? = (sourceZeroTransferCode width entry coldEntry)[phase.val]?) :
    ∀ phase : Fin 4, resident[(entry + 92) + phase.val]? =
      (RawTransferLoops.countedReleaseCode width (entry + 92) (entry + 96))[phase.val]? := by
  let before : Program width 8 := (originalArityPatchCode width 0) ++ (RawAdapterProgram.dependencySerializerCode width (entry + 8) 0) ++ (dependencySaveSetupCode width 0 (entry + 84)) ++ (RawTransferLoops.reverseSaveCode width (entry + 84) (entry + 90)) ++ (dependencyReleaseSetupCode width (entry + 92))
  let fragment : Program width 8 := RawTransferLoops.countedReleaseCode width (entry + 92) (entry + 96)
  let after : Program width 8 := (#[.branchZero 6 (word width coldEntry)])
  have layout : sourceZeroTransferCode width entry coldEntry = (before ++ fragment) ++ after := by
    simp only [sourceZeroTransferCode, before, fragment, after, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 92 := by
    simp only [before, Array.size_append, source_zero_patch_size, source_zero_setup_size,
      source_zero_release_setup_size, RawAdapterProgram.dependencySerializerCode_size,
      RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size]
  have fragmentSize : fragment.size = 4 := by
    simp only [fragment, RawAdapterProgram.dependencySerializerCode_size,
      RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size]
  exact extract_copy_section resident (sourceZeroTransferCode width entry coldEntry)
    before fragment after entry 92 4 layout beforeSize fragmentSize physical

private theorem source_zero_handoff_part (resident : Program width 8) (entry coldEntry : Nat)
    (physical : ∀ phase : Fin (sourceZeroTransferCode width entry coldEntry).size,
      resident[entry + phase.val]? = (sourceZeroTransferCode width entry coldEntry)[phase.val]?) :
    ∀ phase : Fin 1, resident[(entry + 96) + phase.val]? =
      (#[.branchZero 6 (word width coldEntry)])[phase.val]? := by
  let before : Program width 8 := (originalArityPatchCode width 0) ++ (RawAdapterProgram.dependencySerializerCode width (entry + 8) 0) ++ (dependencySaveSetupCode width 0 (entry + 84)) ++ (RawTransferLoops.reverseSaveCode width (entry + 84) (entry + 90)) ++ (dependencyReleaseSetupCode width (entry + 92)) ++ (RawTransferLoops.countedReleaseCode width (entry + 92) (entry + 96))
  let fragment : Program width 8 := #[.branchZero 6 (word width coldEntry)]
  let after : Program width 8 := #[]
  have layout : sourceZeroTransferCode width entry coldEntry = (before ++ fragment) ++ after := by
    simp only [sourceZeroTransferCode, before, fragment, after, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 96 := by
    simp only [before, Array.size_append, source_zero_patch_size, source_zero_setup_size,
      source_zero_release_setup_size, RawAdapterProgram.dependencySerializerCode_size,
      RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size]
  have fragmentSize : fragment.size = 1 := by
    rfl
  exact extract_copy_section resident (sourceZeroTransferCode width entry coldEntry)
    before fragment after entry 96 1 layout beforeSize fragmentSize physical


theorem source_zero_transfer_from_block (resident : Program width 8)
    (entry coldEntry : Nat) (raw : RawDAG) (valid : raw.WellFormed channels)
    (state : State width 8)
    (image : OriginalImageStored state.heap 0 channels raw)
    (originalSize : state.heap.size = (originalPacket width channels raw).size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (codeFits : entry + 97 < 2 ^ width)
    (heapFits : (originalPacket width channels raw).size + 5 + 4 * raw.nodes.size +
      2 * (rowChildren (originalRows raw)).length < 2 ^ width)
    (physical : ∀ phase : Fin (sourceZeroTransferCode width entry coldEntry).size,
      resident[entry + phase.val]? = (sourceZeroTransferCode width entry coldEntry)[phase.val]?) :
    ∃ final peak, Execution resident state final
        (22 * raw.nodes.size + 7 * (rowChildren (originalRows raw)).length +
          6 * (5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length) +
          4 * ((originalPacket width channels raw).size + 5 + 4 * raw.nodes.size +
            2 * (rowChildren (originalRows raw)).length) + 63) peak ∧
      peak ≤ state.liveWords +
        2 * (5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length) ∧
      final.heap = #[] ∧
      final.stack = (Controller.Horn.SourceSerialize.heap (width := width)
        (RawDependencyOrder.dependencyClauses (raw.toUnordered valid))).toList ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width coldEntry ∧ final.halted = false := by
  have patchAt := source_zero_patch_part resident entry coldEntry physical
  have serializerAt := source_zero_serialize_part resident entry coldEntry physical
  have setupAt := source_zero_setup_part resident entry coldEntry physical
  have saveParts := source_zero_save_part resident entry coldEntry physical
  have releaseSetupAt := source_zero_releaseSetup_part resident entry coldEntry physical
  have releaseParts := source_zero_release_part resident entry coldEntry physical
  have handoffParts := source_zero_handoff_part resident entry coldEntry physical
  have saveAt : RawTransferLoops.CodeAt resident (entry + 84)
      (RawTransferLoops.reverseSaveCode width (entry + 84) (entry + 90)) := by
    intro phase
    exact saveParts ⟨phase.val, by
      simpa only [RawTransferLoops.reverseSaveCode_size] using phase.isLt⟩
  have releaseAt : RawTransferLoops.CodeAt resident (entry + 92)
      (RawTransferLoops.countedReleaseCode width (entry + 92) (entry + 96)) := by
    intro phase
    exact releaseParts ⟨phase.val, by
      simpa only [RawTransferLoops.countedReleaseCode_size] using phase.isLt⟩
  have handoffAt : resident[entry + 96]? = some (.branchZero 6 (word width coldEntry)) := by
    have selected := handoffParts ⟨0, by decide⟩
    change resident[(entry + 96) + 0]? = some (.branchZero 6 (word width coldEntry)) at selected
    simpa only [Nat.add_zero] using selected
  exact source_zero_transfer_execution resident entry coldEntry raw valid state image
    originalSize position running codeFits heapFits
    (by simpa only [Nat.add_zero] using patchAt) serializerAt setupAt saveAt
    releaseSetupAt releaseAt handoffAt

private theorem source_transfer_ticks_exact (width channels : Nat) (raw : RawDAG) :
    sourceTransferTicks width channels raw =
      86 * raw.nodes.size + 31 * (rowChildren (originalRows raw)).length +
        4 * (rowGuards (originalRows raw)).length + 4 * raw.roots.length + 149 := by
  simp only [sourceTransferTicks, dependencyPacketLength, original_packet_size]
  omega

private theorem source_transfer_linear (width channels : Nat) (raw : RawDAG) :
    sourceTransferTicks width channels raw ≤ 149 *
      (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
        (rowGuards (originalRows raw)).length + raw.roots.length + 1) := by
  rw [source_transfer_ticks_exact]
  omega

private theorem source_transfer_heap_linear (width channels : Nat) (raw : RawDAG) :
    (originalPacket width channels raw).size + dependencyPacketLength raw ≤ 14 *
      (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
        (rowGuards (originalRows raw)).length + raw.roots.length + 1) := by
  simp only [original_packet_size, dependencyPacketLength]
  omega

private theorem source_transfer_peak_linear (channels : Nat) (raw : RawDAG) :
    2 * dependencyPacketLength raw ≤ 10 *
      (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
        (rowGuards (originalRows raw)).length + raw.roots.length + 1) := by
  simp only [dependencyPacketLength]
  omega

private theorem source_execution_capacity (channels : Nat) (raw : RawDAG) :
    4096 * (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
      (rowGuards (originalRows raw)).length + raw.roots.length + 1) <
        2 ^ rawExecutionWidth channels raw := by
  let G := channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
    (rowGuards (originalRows raw)).length + raw.roots.length + 1
  have basic := Nat.lt_pow_succ_log_self (by decide : 1 < 2) G
  have scaled := Nat.mul_lt_mul_of_pos_left basic (by decide : 0 < 4096)
  have identity : 4096 * 2 ^ (Nat.log 2 G + 1) =
      2 ^ rawExecutionWidth channels raw := by
    simp only [rawExecutionWidth, G, Nat.pow_add, Nat.pow_one, Nat.reducePow]
    omega
  simpa only [identity] using scaled

private theorem source_transfer_heap_fits (channels : Nat) (raw : RawDAG) :
    (originalPacket (rawExecutionWidth channels raw) channels raw).size +
      dependencyPacketLength raw < 2 ^ rawExecutionWidth channels raw := by
  have bound := source_transfer_heap_linear (rawExecutionWidth channels raw) channels raw
  have capacity := source_execution_capacity channels raw
  omega

/-- The concrete 97-instruction transfer block derives every fetched section
and its heap capacity from the original input size. Original packet construction
and the caller's entry transfer precede this boundary. -/
theorem source_zero_block_execution (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry coldEntry : Nat)
    (state : State (rawExecutionWidth channels raw) 8)
    (image : OriginalImageStored state.heap 0 channels raw)
    (originalSize : state.heap.size =
      (originalPacket (rawExecutionWidth channels raw) channels raw).size)
    (position : state.pc = word (rawExecutionWidth channels raw) entry)
    (running : state.halted = false)
    (codeFits : entry + 97 < 2 ^ rawExecutionWidth channels raw)
    (physical : ∀ phase : Fin (sourceZeroTransferCode
        (rawExecutionWidth channels raw) entry coldEntry).size,
      resident[entry + phase.val]? =
        (sourceZeroTransferCode (rawExecutionWidth channels raw) entry coldEntry)[phase.val]?) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 149 * (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
        (rowGuards (originalRows raw)).length + raw.roots.length + 1) ∧
      peak ≤ state.liveWords + 10 *
        (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
          (rowGuards (originalRows raw)).length + raw.roots.length + 1) ∧
      final.heap = #[] ∧
      final.stack = (Controller.Horn.SourceSerialize.heap
        (width := rawExecutionWidth channels raw)
        (RawDependencyOrder.dependencyClauses (raw.toUnordered valid))).toList ++ state.stack ∧
      final.output = state.output ∧
      final.pc = word (rawExecutionWidth channels raw) coldEntry ∧ final.halted = false := by
  have heapFits := source_transfer_heap_fits channels raw
  change (originalPacket (rawExecutionWidth channels raw) channels raw).size +
      (5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length) <
        2 ^ rawExecutionWidth channels raw at heapFits
  obtain ⟨final, peak, trace, space, heap, stack, output, pc, halted⟩ :=
    source_zero_transfer_from_block resident entry coldEntry raw valid state image
      originalSize position running codeFits (by simpa only [Nat.add_assoc] using heapFits) physical
  refine ⟨final, sourceTransferTicks (rawExecutionWidth channels raw) channels raw,
    peak, ?_, source_transfer_linear _ _ _, ?_, heap, stack, output, pc, halted⟩
  · simpa only [sourceTransferTicks, dependencyPacketLength, Nat.add_assoc] using trace
  · have additional := source_transfer_peak_linear channels raw
    change 2 * (5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length) ≤ _ at additional
    omega

theorem source_zero_runtime_from_block (raw : RawDAG) (valid : raw.WellFormed channels)
    (assignment : Assignment channels)
    (clauses : List (Controller.CNF.Clause (Fin (raw.toUnordered valid).nodeCount)))
    (source : clauses = RawDependencyOrder.dependencyClauses (raw.toUnordered valid))
    (resident : Program (rawExecutionWidth channels raw) 8) (delta conflict : Nat)
    (state : State (rawExecutionWidth channels raw) 8) (suffix : List (Word (rawExecutionWidth channels raw)))
    (entry : Nat)
    (image : OriginalImageStored state.heap 0 channels raw)
    (originalSize : state.heap.size = (originalPacket (rawExecutionWidth channels raw) channels raw).size)
    (input : state.stack = (originalPacket (rawExecutionWidth channels raw) channels raw).toList ++
      (List.ofFn (fun channel => boolWord (rawExecutionWidth channels raw) (assignment channel)) ++ suffix))
    (position : state.pc = word (rawExecutionWidth channels raw) entry) (running : state.halted = false)
    (transferFits : entry + 97 < 2 ^ rawExecutionWidth channels raw)
    (transferAt : ∀ phase : Fin (sourceZeroTransferCode
        (rawExecutionWidth channels raw) entry delta).size,
      resident[entry + phase.val]? =
        (sourceZeroTransferCode (rawExecutionWidth channels raw) entry delta)[phase.val]?)
    (coldAt : sourceRelocatedCodeAt resident (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses) delta)
    (pushAt : resident[delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size]? = some (.push 7))
    (setupAt : ∀ phase : Fin 9,
      resident[(delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 1) + phase.val]? =
        (Controller.Horn.WorklistSeed.coldSetupCode (n := (raw.toUnordered valid).nodeCount) (rawExecutionWidth channels raw) (Controller.Horn.SourceSerialize.base clauses)
          (Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses)
          (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 10))[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := (raw.toUnordered valid).nodeCount) resident
      (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 10)
      (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57) conflict)
    (capacity : delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57 < 2 ^ (rawExecutionWidth channels raw))
    (heapFits : Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum < 2 ^ (rawExecutionWidth channels raw))
    (runtimeAt : ∀ phase : Fin 61,
      resident[(delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57) + phase.val]? =
        (sourceDependencyRuntimeCode (rawExecutionWidth channels raw) (raw.toUnordered valid).nodeCount (Controller.Horn.SourceSerialize.base clauses)
          (delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 57) conflict)[phase.val]?)
    (runtimeCapacity : delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 118 < 2 ^ (rawExecutionWidth channels raw))
    (accept tag : Nat)
    (cycleAt : ∀ phase : Fin 8,
      resident[(delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 118) + phase.val]? =
        (sourceCycleCode (rawExecutionWidth channels raw)
          (Controller.Horn.WorklistBucketReady.tailSlot (n := (raw.toUnordered valid).nodeCount) (Controller.Horn.SourceSerialize.base clauses))
          (Controller.Horn.WorklistMark.queueStart (n := (raw.toUnordered valid).nodeCount) (Controller.Horn.SourceSerialize.base clauses) + (raw.toUnordered valid).nodeCount)
          accept tag)[phase.val]?)
    (cycleCapacity : delta + (Controller.Horn.IndexScanCold.program (rawExecutionWidth channels raw) clauses).size + 126 < 2 ^ (rawExecutionWidth channels raw))
    (rankDone : Nat)
    (rankCapacity : accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 19 < 2 ^ (rawExecutionWidth channels raw))
    (rankRoom : Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum + ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + (raw.toUnordered valid).nodeCount < 2 ^ (rawExecutionWidth channels raw))
    (popAt : resident[accept]? = some (.pop 4))
    (reloadAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident (accept + 1)
      (Controller.Cost.InputLoad.code (width := rawExecutionWidth channels raw) ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length))
    (zeroAt : Controller.Cost.ForestZeroCallerWiden.WidenedBlockAt resident
      (accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length) (Controller.Cost.Initialize.code (word (rawExecutionWidth channels raw) 0) (raw.toUnordered valid).nodeCount))
    (rankSetupAt : ∀ phase : Fin 11,
      resident[(accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount) + phase.val]? =
        (sourceRankSetupCode (rawExecutionWidth channels raw) (raw.toUnordered valid).nodeCount (Controller.Horn.SourceSerialize.base clauses) ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length
          (accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 11))[phase.val]?)
    (rankAt : ∀ phase : Fin 8,
      resident[(accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 11) + phase.val]? =
        (RawAdapterProgram.rankCopyCode (rawExecutionWidth channels raw) (accept + 1 + 2 * ((originalPacket (rawExecutionWidth channels raw) channels raw).toList).length + 2 * (raw.toUnordered valid).nodeCount + 11) rankDone)[phase.val]?)
    (copyAt : ∀ phase : Fin (typedCopyColdCode (rawExecutionWidth channels raw)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length
        (Controller.Horn.SourceSerialize.base clauses) rankDone).size,
      resident[rankDone + phase.val]? =
        (typedCopyColdCode (rawExecutionWidth channels raw) channels raw.nodes.size
          (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
          raw.roots.length (Controller.Horn.SourceSerialize.base clauses) rankDone)[phase.val]?)
    (copyCapacity : rankDone + (typedCopyColdCode (rawExecutionWidth channels raw)
        channels raw.nodes.size (rowChildren (originalRows raw)).length
        (rowGuards (originalRows raw)).length raw.roots.length
        (Controller.Horn.SourceSerialize.base clauses) rankDone).size <
      2 ^ rawExecutionWidth channels raw)
    (copyRoom : channels + Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses +
        3 * clauses.length + 3 * (clauses.map List.length).sum +
        (originalPacket (rawExecutionWidth channels raw) channels raw).size + raw.nodes.size +
        (5 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
          (rowGuards (originalRows raw)).length + raw.roots.length) < 2 ^ rawExecutionWidth channels raw) :
    ((raw.toUnordered valid).Acyclic ∧
      ∃ numbering : (raw.toUnordered valid).Numbering,
        ∃ final ticks peak, Execution resident state final ticks peak ∧
          ticks ≤ sourceTransferTicks (rawExecutionWidth channels raw) channels raw + 61 * raw.nodes.size + 115 * (clauses.map List.length).sum + 131 * clauses.length +
            2 * (originalPacket (rawExecutionWidth channels raw) channels raw).size +
            321 * numbering.toDAG.countedSize +
            4 * (Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) clauses +
              3 * clauses.length + 3 * (clauses.map List.length).sum +
              (originalPacket (rawExecutionWidth channels raw) channels raw).size + raw.nodes.size) +
            226 * (numbering.toDAG.roots.map (typedConeIncidenceSize numbering.toDAG)).sum + 305 ∧
          peak ≤ max (state.liveWords + 3 * dependencyPacketLength raw + 6 * raw.nodes.size + 6 +
              3 * clauses.length + 3 * (clauses.map List.length).sum +
              2 * (numberedPacketWords (width := rawExecutionWidth channels raw) raw valid numbering).length)
            (38 * numbering.toDAG.countedSize + 1884 + suffix.length + state.output.length) ∧
          final.stack = suffix ∧
          final.output = (numbering.toDAG.roots.map (fun node =>
            boolWord (rawExecutionWidth channels raw) (numbering.toDAG.eval assignment node))).reverse ++
            state.output ∧ final.halted = true) ∨
    (¬(raw.toUnordered valid).Acyclic ∧ ∃ final ticks peak,
      Execution resident state final ticks peak ∧
      ticks ≤ sourceTransferTicks (rawExecutionWidth channels raw) channels raw + 51 * raw.nodes.size + 115 * (clauses.map List.length).sum + 131 * clauses.length + 98 ∧
      peak ≤ state.liveWords + 3 * dependencyPacketLength raw + 5 * raw.nodes.size + 6 +
        3 * clauses.length + 3 * (clauses.map List.length).sum ∧
      final.output = word (rawExecutionWidth channels raw) tag :: state.output ∧ final.halted = true) := by
  have patchAt := source_zero_patch_part resident entry delta transferAt
  have serializerAt := source_zero_serialize_part resident entry delta transferAt
  have saveSetupAt := source_zero_setup_part resident entry delta transferAt
  have saveParts := source_zero_save_part resident entry delta transferAt
  have releaseSetupAt := source_zero_releaseSetup_part resident entry delta transferAt
  have releaseParts := source_zero_release_part resident entry delta transferAt
  have handoffParts := source_zero_handoff_part resident entry delta transferAt
  have saveAt : RawTransferLoops.CodeAt resident (entry + 84)
      (RawTransferLoops.reverseSaveCode (rawExecutionWidth channels raw) (entry + 84) (entry + 90)) := by
    intro phase
    exact saveParts ⟨phase.val, by
      simpa only [RawTransferLoops.reverseSaveCode_size] using phase.isLt⟩
  have releaseAt : RawTransferLoops.CodeAt resident (entry + 92)
      (RawTransferLoops.countedReleaseCode (rawExecutionWidth channels raw) (entry + 92) (entry + 96)) := by
    intro phase
    exact releaseParts ⟨phase.val, by
      simpa only [RawTransferLoops.countedReleaseCode_size] using phase.isLt⟩
  have handoffAt : resident[entry + 96]? = some
      (.branchZero 6 (word (rawExecutionWidth channels raw) delta)) := by
    have selected := handoffParts ⟨0, by decide⟩
    change resident[(entry + 96) + 0]? = some
      (.branchZero 6 (word (rawExecutionWidth channels raw) delta)) at selected
    simpa only [Nat.add_zero] using selected
  have transferHeapFits := source_transfer_heap_fits channels raw
  change (originalPacket (rawExecutionWidth channels raw) channels raw).size +
      (5 + 4 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length) <
        2 ^ rawExecutionWidth channels raw at transferHeapFits
  exact source_zero_runtime_execution raw valid assignment clauses source resident delta conflict
    state suffix entry image originalSize input position running transferFits
    (by simpa only [Nat.add_assoc] using transferHeapFits)
    (by simpa only [Nat.add_zero] using patchAt) serializerAt saveSetupAt saveAt
    releaseSetupAt releaseAt handoffAt coldAt pushAt setupAt scanAt capacity heapFits
    runtimeAt runtimeCapacity accept tag cycleAt cycleCapacity rankDone rankCapacity
    rankRoom popAt reloadAt zeroAt rankSetupAt rankAt copyAt copyCapacity copyRoom

private theorem typed_shape_warm_size (width entry nodeBase temporary : Nat)
    (layout : UniformDAGNode.Layout) : (typedWarmCode width entry nodeBase temporary layout).size = 125 := by
  have commitSize : (commitResultCode width temporary nodeBase).size = 6 := rfl
  simp only [typedWarmCode, Array.size_append, widenProgram, Array.size_map,
    List.size_toArray, UniformDAGNode.code_length, commitSize] <;> rfl

private theorem typed_shape_outer_size (width base channels nodes children guards roots : Nat) :
    (typedShapeOuter width base channels nodes children guards roots).size = 298 := by
  have dfsSize : (typedShapeDFS width (base + 4) channels nodes children guards roots).size = 120 := by
    simp only [typedShapeDFS, dfsProgram_size]
  simp only [typedShapeOuter, Array.size_append, dfsSize, typed_shape_warm_size,
    SparseConeReuse.resetNodesCode_size, SparseConeReuse.resetChannelsCode_size,
    SparseConeReuse.clearLedgerCountsCode_size] <;> rfl

private theorem typed_shape_code_size (width channels nodes children guards roots : Nat) :
    (typedShapeCode width channels nodes children guards roots).size = 466 + 6 * channels + 6 * nodes := by
  unfold typedShapeCode
  simp only [Array.size_append, widenProgram, Array.size_map, List.size_toArray,
    List.length_append, ForestInputMetadata.fullCode_length, InputLoad.code_length,
    UniformDAGLoop.code_length, Initialize.code_length, typed_shape_outer_size,
    List.length_cons, List.length_nil]
  omega

theorem source_dependency_runtime_size (width nodes base entry conflict : Nat) :
    (sourceDependencyRuntimeCode width nodes base entry conflict).size = 61 := by
  simp only [sourceDependencyRuntimeCode, Array.size_append,
    Controller.Horn.WorklistAccept.head_setup_size, Controller.Horn.WorklistFIFO.fetch_size,
    Controller.Horn.WorklistBucketLoop.code_size, Controller.Horn.WorklistBucketReady.code_size,
    Controller.Horn.WorklistFIFO.advance_size]

theorem source_cycle_size (width tail expected accept tag : Nat) :
    (sourceCycleCode width tail expected accept tag).size = 8 := rfl

/-- The resident source adapter consists of the original packet transfer,
relocated dependency classifier, produced-rank copy and typed evaluator. Its
instruction values depend on counted sizes and code offsets; original IDs,
ordered duplicate incidences and roots remain packet data. -/
@[irreducible] def sourceCallerCode (raw : RawDAG) (valid : raw.WellFormed channels)
    (entry tag : Nat) : Program (rawExecutionWidth channels raw) 8 :=
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  sourceZeroTransferCode width entry delta ++
    cold.map (RawAdapterProgram.relocatedInstruction delta) ++ #[.push 7] ++
    Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base
      (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10) ++
    Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10)
      (delta + cold.size + 57) conflict ++
    sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict ++
    sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base)
      (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag ++
    #[.pop 4] ++ widenProgram (InputLoad.code (width := width) W).toArray ++
    widenProgram (Initialize.code (word width 0) V).toArray ++
    sourceRankSetupCode width V base W rankEntry ++
    RawAdapterProgram.rankCopyCode width rankEntry rankDone ++ copied ++
    #[.constant 0 (word width tag), .emit 0, .halt]

private theorem source_dependency_dimensions (raw : RawDAG) (valid : raw.WellFormed channels) :
    (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).length = raw.nodes.size ∧
    ((RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).map List.length).sum =
      raw.nodes.size + (rowChildren (originalRows raw)).length := by
  let rows := (originalRows raw).map Row.children
  have rowCount : rows.length = raw.nodes.size := by
    simp only [rows, List.length_map, original_rows_length]
  have clauseCount : (RawDependencyOrder.dependencyClauses
      (raw.toUnordered valid)).length = raw.nodes.size := by
    simp only [RawDependencyOrder.dependencyClauses, List.length_ofFn, RawDAG.toUnordered]
  have lengths : (RawDependencyOrder.dependencyClauses
      (raw.toUnordered valid)).map List.length =
        rows.map (fun children => children.length + 1) := by
    rw [show rows = List.ofFn (fun parent : Fin (raw.toUnordered valid).nodeCount =>
      ((raw.toUnordered valid).node parent).children.map Fin.val)
      from original_dependency_rows raw valid]
    simp only [RawDependencyOrder.dependencyClauses, RawDependencyOrder.dependencyClause,
      List.map_ofFn, List.length_cons, List.length_map, Function.comp_def, Nat.add_comm]
  have total : (rows.map List.length).sum =
      (rowChildren (originalRows raw)).length := original_child_row_total _
  refine ⟨clauseCount, ?_⟩
  rw [lengths, dependency_parent_length_sum, total, rowCount]
  omega

theorem source_rank_setup_size (width nodes base W rankEntry : Nat) :
    (sourceRankSetupCode width nodes base W rankEntry).size = 11 := rfl

/-- Full resident source-adapter size, counting every duplicate incidence in its
source-dependent loaders. No produced numbering changes the instruction array. -/
theorem source_caller_code_size (raw : RawDAG) (valid : raw.WellFormed channels)
    (entry tag : Nat) : (sourceCallerCode raw valid entry tag).size =
      1208 + 6 * channels + 32 * raw.nodes.size +
        8 * (rowChildren (originalRows raw)).length +
        2 * (rowGuards (originalRows raw)).length + 2 * raw.roots.length := by
  have dimensions := source_dependency_dimensions raw valid
  unfold sourceCallerCode
  simp only [Array.size_append, Array.size_map, source_zero_code_size,
    Controller.Horn.IndexScanCold.program_size, Controller.Horn.IndexScanCold.entry,
    Controller.Horn.NormalizeCold.program_size, Controller.Horn.WorklistSeed.cold_setup_size,
    Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size,
    source_cycle_size, widenProgram, List.size_toArray, InputLoad.code_length,
    Initialize.code_length, source_rank_setup_size, RawAdapterProgram.rankCopyCode_size,
    typedCopyColdCode_size, typed_shape_code_size, original_packet_size,
    dimensions.1, dimensions.2, List.length_cons, List.length_nil]
  have literalCount := dimensions.2
  omega

private theorem source_caller_code_linear (raw : RawDAG) (valid : raw.WellFormed channels)
    (entry tag : Nat) : (sourceCallerCode raw valid entry tag).size ≤ 1208 *
      (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
        (rowGuards (originalRows raw)).length + raw.roots.length + 1) := by
  rw [source_caller_code_size]
  omega

private theorem source_caller_transfer_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (97), resident[(entry + (0)) + phase.val]? = (sourceZeroTransferCode width entry delta)[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := #[]
  let fragment : Program width 8 := sourceZeroTransferCode width entry delta
  let after : Program width 8 := (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = 0 := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 97 := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry (0) (97) layout beforeSize fragmentSize physical

private theorem source_caller_cold_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (cold.size), resident[(entry + ((97))) + phase.val]? = (cold.map (RawAdapterProgram.relocatedInstruction delta))[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta)
  let fragment : Program width 8 := cold.map (RawAdapterProgram.relocatedInstruction delta)
  let after : Program width 8 := (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = cold.size := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97)) (cold.size) layout beforeSize fragmentSize physical

private theorem source_caller_push_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (1), resident[(entry + ((97) + (cold.size))) + phase.val]? = (#[.push 7])[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta))
  let fragment : Program width 8 := #[.push 7]
  let after : Program width 8 := (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 1 := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size)) (1) layout beforeSize fragmentSize physical

private theorem source_caller_setup_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (9), resident[(entry + ((97) + (cold.size) + (1))) + phase.val]? = (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10))[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7])
  let fragment : Program width 8 := Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)
  let after : Program width 8 := (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) + (1) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 9 := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size) + (1)) (9) layout beforeSize fragmentSize physical

private theorem source_caller_seed_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (47), resident[(entry + ((97) + (cold.size) + (1) + (9))) + phase.val]? = (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict)[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10))
  let fragment : Program width 8 := Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict
  let after : Program width 8 := (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) + (1) + (9) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 47 := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size) + (1) + (9)) (47) layout beforeSize fragmentSize physical

private theorem source_caller_fifo_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (61), resident[(entry + ((97) + (cold.size) + (1) + (9) + (47))) + phase.val]? = (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict)[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict)
  let fragment : Program width 8 := sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict
  let after : Program width 8 := (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) + (1) + (9) + (47) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 61 := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size) + (1) + (9) + (47)) (61) layout beforeSize fragmentSize physical

private theorem source_caller_cycle_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (8), resident[(entry + ((97) + (cold.size) + (1) + (9) + (47) + (61))) + phase.val]? = (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag)[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict)
  let fragment : Program width 8 := sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag
  let after : Program width 8 := (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) + (1) + (9) + (47) + (61) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 8 := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size) + (1) + (9) + (47) + (61)) (8) layout beforeSize fragmentSize physical

private theorem source_caller_pop_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (1), resident[(entry + ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8))) + phase.val]? = (#[.pop 4])[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag)
  let fragment : Program width 8 := #[.pop 4]
  let after : Program width 8 := (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) + (1) + (9) + (47) + (61) + (8) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 1 := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8)) (1) layout beforeSize fragmentSize physical

private theorem source_caller_reload_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (2 * W), resident[(entry + ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1))) + phase.val]? = (widenProgram (InputLoad.code (width := width) W).toArray)[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4])
  let fragment : Program width 8 := widenProgram (InputLoad.code (width := width) W).toArray
  let after : Program width 8 := (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 2 * W := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1)) (2 * W) layout beforeSize fragmentSize physical

private theorem source_caller_zero_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (2 * V), resident[(entry + ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W))) + phase.val]? = (widenProgram (Initialize.code (word width 0) V).toArray)[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray)
  let fragment : Program width 8 := widenProgram (Initialize.code (word width 0) V).toArray
  let after : Program width 8 := (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 2 * V := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W)) (2 * V) layout beforeSize fragmentSize physical

private theorem source_caller_rankSetup_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (11), resident[(entry + ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V))) + phase.val]? = (sourceRankSetupCode width V base W rankEntry)[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray)
  let fragment : Program width 8 := sourceRankSetupCode width V base W rankEntry
  let after : Program width 8 := (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 11 := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V)) (11) layout beforeSize fragmentSize physical

private theorem source_caller_rank_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (8), resident[(entry + ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V) + (11))) + phase.val]? = (RawAdapterProgram.rankCopyCode width rankEntry rankDone)[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry)
  let fragment : Program width 8 := RawAdapterProgram.rankCopyCode width rankEntry rankDone
  let after : Program width 8 := (copied) ++ (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V) + (11) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 8 := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V) + (11)) (8) layout beforeSize fragmentSize physical

private theorem source_caller_copy_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (copied.size), resident[(entry + ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V) + (11) + (8))) + phase.val]? = (copied)[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone)
  let fragment : Program width 8 := copied
  let after : Program width 8 := (#[.constant 0 (word width tag), .emit 0, .halt])
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V) + (11) + (8) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = copied.size := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V) + (11) + (8)) (copied.size) layout beforeSize fragmentSize physical

private theorem source_caller_conflict_part (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  ∀ phase : Fin (3), resident[(entry + ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V) + (11) + (8) + (copied.size))) + phase.val]? = (#[.constant 0 (word width tag), .emit 0, .halt])[phase.val]? := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  let before : Program width 8 := (sourceZeroTransferCode width entry delta) ++ (cold.map (RawAdapterProgram.relocatedInstruction delta)) ++ (#[.push 7]) ++ (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10)) ++ (Controller.Horn.WorklistSeed.code (n := V) width base (delta + cold.size + 10) (delta + cold.size + 57) conflict) ++ (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict) ++ (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base) (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag) ++ (#[.pop 4]) ++ (widenProgram (InputLoad.code (width := width) W).toArray) ++ (widenProgram (Initialize.code (word width 0) V).toArray) ++ (sourceRankSetupCode width V base W rankEntry) ++ (RawAdapterProgram.rankCopyCode width rankEntry rankDone) ++ (copied)
  let fragment : Program width 8 := #[.constant 0 (word width tag), .emit 0, .halt]
  let after : Program width 8 := #[]
  have layout : sourceCallerCode raw valid entry tag = (before ++ fragment) ++ after := by
    simp only [sourceCallerCode, before, fragment, after, width, clauses, cold, W, V,
      base, delta, accept, rankEntry, rankDone, copied, conflict, Array.append_assoc,
      Array.empty_append, Array.append_empty]
  have beforeSize : before.size = (97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V) + (11) + (8) + (copied.size) := by
    simp only [before, Array.size_append, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> omega
  have fragmentSize : fragment.size = 3 := by
    simp only [fragment, source_zero_code_size, Array.size_map, Controller.Horn.WorklistSeed.cold_setup_size,
      Controller.Horn.WorklistSeed.code_size, source_dependency_runtime_size, source_cycle_size,
      widenProgram, List.size_toArray, InputLoad.code_length, Initialize.code_length,
      source_rank_setup_size, RawAdapterProgram.rankCopyCode_size, List.length_cons, List.length_nil] <;> first | rfl | omega
  exact extract_copy_section resident (sourceCallerCode raw valid entry tag)
    before fragment after entry ((97) + (cold.size) + (1) + (9) + (47) + (61) + (8) + (1) + (2 * W) + (2 * V) + (11) + (8) + (copied.size)) (3) layout beforeSize fragmentSize physical


private theorem source_transfer_fixed_section (resident : Program width 8) (entry delta : Nat)
    (physical : ∀ phase : Fin 97, resident[entry + phase.val]? =
      (sourceZeroTransferCode width entry delta)[phase.val]?) :
    ∀ phase : Fin (sourceZeroTransferCode width entry delta).size,
      resident[entry + phase.val]? = (sourceZeroTransferCode width entry delta)[phase.val]? := by
  intro phase
  have inside : phase.val < 97 := by
    simpa only [source_zero_code_size] using phase.isLt
  exact physical ⟨phase.val, inside⟩

theorem source_seed_fixed_section (resident : Program width 8)
    (nodes base entry done conflict : Nat)
    (physical : ∀ phase : Fin 47, resident[entry + phase.val]? =
      (Controller.Horn.WorklistSeed.code (n := nodes) width base entry done conflict)[phase.val]?) :
    Controller.Horn.WorklistSeed.At (n := nodes) resident base entry done conflict := physical

private theorem source_widen_instruction_eq (instruction : Instruction width 4) :
    SparseConeTraversal.widenInstruction instruction = RegisterWiden.widenInstruction instruction := by
  cases instruction <;> rfl

theorem source_widened_section (resident : Program width 8) (entry : Nat)
    (low : GateProgram.Code width)
    (physical : ∀ phase : Fin (widenProgram low.toArray).size,
      resident[entry + phase.val]? = (widenProgram low.toArray)[phase.val]?) :
    ForestZeroCallerWiden.WidenedBlockAt resident entry low := by
  intro offset inside
  have bound : offset < (widenProgram low.toArray).size := by
    simpa only [widenProgram, Array.size_map, List.size_toArray] using inside
  have same : SparseConeTraversal.widenInstruction (width := width) = RegisterWiden.widenInstruction := by
    funext instruction
    exact source_widen_instruction_eq instruction
  simpa only [widenProgram, Array.getElem?_map, List.getElem?_toArray, same] using
    physical ⟨offset, bound⟩

theorem source_relocated_section (resident sourceProgram : Program width 8) (entry : Nat)
    (physical : ∀ phase : Fin sourceProgram.size,
      resident[entry + phase.val]? =
        (sourceProgram.map (RawAdapterProgram.relocatedInstruction entry))[phase.val]?) :
    sourceRelocatedCodeAt resident sourceProgram entry := by
  intro offset inside
  have selected := physical ⟨offset, inside⟩
  rw [Array.getElem?_map, Array.getElem?_eq_getElem inside, Option.map_some] at selected
  exact selected

private theorem source_record_start_exact (raw : RawDAG) (valid : raw.WellFormed channels) :
    Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw)
      (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)) =
      9 + 9 * raw.nodes.size + 2 * (rowChildren (originalRows raw)).length := by
  have dimensions := source_dependency_dimensions raw valid
  have nodes : (raw.toUnordered valid).nodeCount = raw.nodes.size := rfl
  simp only [Controller.Horn.IndexScanCold.recordStart, Controller.Horn.NormalizeCold.words_eq,
    dimensions.1, dimensions.2, nodes]
  omega

private theorem source_heap_rooms (raw : RawDAG) (valid : raw.WellFormed channels) :
    let width := rawExecutionWidth channels raw
    let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
    let upper := Controller.Horn.IndexScanCold.recordStart width clauses +
      3 * clauses.length + 3 * (clauses.map List.length).sum
    let W := (originalPacket width channels raw).size
    upper < 2 ^ width ∧ upper + W + raw.nodes.size < 2 ^ width ∧
      channels + upper + W + raw.nodes.size +
        (5 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
          (rowGuards (originalRows raw)).length + raw.roots.length) < 2 ^ width := by
  have dimensions := source_dependency_dimensions raw valid
  have capacity := source_execution_capacity channels raw
  dsimp only
  simp only [source_record_start_exact, original_packet_size, dimensions.1, dimensions.2]
  omega

private theorem source_numbered_size (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    numbering.toDAG.countedSize = channels + raw.nodes.size +
      (rowChildren (originalRows raw)).length + (rowGuards (originalRows raw)).length + raw.roots.length := by
  have rowEq : RawNumberingCounts.rowOfGate = originalRow := by
    funext gate
    cases gate <;> rfl
  have rowsEq : RawNumberingCounts.rawRows raw = originalRows raw := by
    simp only [RawNumberingCounts.rawRows, originalRows, rowEq]
  rw [RawNumberingCounts.numbered_size]
  simp only [RawNumberingCounts.rawChildren, RawNumberingCounts.rawGuards, rowsEq]

structure SourceCallerSections (width channels n : Nat) (resident : Program width 8)
    (entry delta conflict accept tag rankDone rawWords typedWords : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) (copied : Program width 8) : Prop where
  transferFits : entry + 97 < 2 ^ width
  transferAt : ∀ phase : Fin (sourceZeroTransferCode width entry delta).size,
    resident[entry + phase.val]? = (sourceZeroTransferCode width entry delta)[phase.val]?
  coldAt : sourceRelocatedCodeAt resident (Controller.Horn.IndexScanCold.program width clauses) delta
  pushAt : resident[delta + (Controller.Horn.IndexScanCold.program width clauses).size]? = some (.push 7)
  setupAt : ∀ phase : Fin 9,
    resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 1) + phase.val]? =
    (Controller.Horn.WorklistSeed.coldSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses)
      (Controller.Horn.IndexScanCold.recordStart width clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10))[phase.val]?
  seedAt : Controller.Horn.WorklistSeed.At (n := n) resident (Controller.Horn.SourceSerialize.base clauses)
    (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10)
    (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict
  seedFits : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57 < 2 ^ width
  heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length + 3 * (clauses.map List.length).sum < 2 ^ width
  fifoAt : ∀ phase : Fin 61,
    resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) + phase.val]? =
    (sourceDependencyRuntimeCode width n (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict)[phase.val]?
  fifoFits : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118 < 2 ^ width
  cycleAt : ∀ phase : Fin 8,
    resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118) + phase.val]? =
    (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := n) (Controller.Horn.SourceSerialize.base clauses))
      (Controller.Horn.WorklistMark.queueStart (n := n) (Controller.Horn.SourceSerialize.base clauses) + n) accept tag)[phase.val]?
  cycleFits : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 126 < 2 ^ width
  rankFits : accept + 1 + 2 * rawWords + 2 * n + 19 < 2 ^ width
  rankRoom : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
    3 * (clauses.map List.length).sum + rawWords + n < 2 ^ width
  popAt : resident[accept]? = some (.pop 4)
  reloadAt : ForestZeroCallerWiden.WidenedBlockAt resident (accept + 1) (InputLoad.code (width := width) rawWords)
  zeroAt : ForestZeroCallerWiden.WidenedBlockAt resident (accept + 1 + 2 * rawWords) (Initialize.code (word width 0) n)
  rankSetupAt : ∀ phase : Fin 11,
    resident[(accept + 1 + 2 * rawWords + 2 * n) + phase.val]? =
    (sourceRankSetupCode width n (Controller.Horn.SourceSerialize.base clauses) rawWords
      (accept + 1 + 2 * rawWords + 2 * n + 11))[phase.val]?
  rankAt : ∀ phase : Fin 8,
    resident[(accept + 1 + 2 * rawWords + 2 * n + 11) + phase.val]? =
    (RawAdapterProgram.rankCopyCode width (accept + 1 + 2 * rawWords + 2 * n + 11) rankDone)[phase.val]?
  copyAt : ∀ phase : Fin copied.size, resident[rankDone + phase.val]? = copied[phase.val]?
  copyFits : rankDone + copied.size < 2 ^ width
  copyRoom : channels + (Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
    3 * (clauses.map List.length).sum + rawWords + n) + typedWords < 2 ^ width

private structure SourceCallerPrefixSections (width channels n : Nat) (resident : Program width 8)
    (entry delta conflict accept tag rankDone rawWords typedWords : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) (copied : Program width 8) : Prop where
  transferFits : entry + 97 < 2 ^ width
  transferAt : ∀ phase : Fin (sourceZeroTransferCode width entry delta).size,
    resident[entry + phase.val]? = (sourceZeroTransferCode width entry delta)[phase.val]?
  coldAt : sourceRelocatedCodeAt resident (Controller.Horn.IndexScanCold.program width clauses) delta
  pushAt : resident[delta + (Controller.Horn.IndexScanCold.program width clauses).size]? = some (.push 7)
  setupAt : ∀ phase : Fin 9,
    resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 1) + phase.val]? =
    (Controller.Horn.WorklistSeed.coldSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses)
      (Controller.Horn.IndexScanCold.recordStart width clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10))[phase.val]?
  seedAt : Controller.Horn.WorklistSeed.At (n := n) resident (Controller.Horn.SourceSerialize.base clauses)
    (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10)
    (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict
  seedFits : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57 < 2 ^ width
  heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length + 3 * (clauses.map List.length).sum < 2 ^ width
  fifoAt : ∀ phase : Fin 61,
    resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) + phase.val]? =
    (sourceDependencyRuntimeCode width n (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict)[phase.val]?
  fifoFits : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118 < 2 ^ width
  cycleAt : ∀ phase : Fin 8,
    resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118) + phase.val]? =
    (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := n) (Controller.Horn.SourceSerialize.base clauses))
      (Controller.Horn.WorklistMark.queueStart (n := n) (Controller.Horn.SourceSerialize.base clauses) + n) accept tag)[phase.val]?
  cycleFits : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 126 < 2 ^ width

private structure SourceCallerTransferSections (width n : Nat) (resident : Program width 8)
    (entry delta : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Prop where
  transferFits : entry + 97 < 2 ^ width
  transferAt : ∀ phase : Fin (sourceZeroTransferCode width entry delta).size,
    resident[entry + phase.val]? = (sourceZeroTransferCode width entry delta)[phase.val]?
  coldAt : sourceRelocatedCodeAt resident (Controller.Horn.IndexScanCold.program width clauses) delta
  pushAt : resident[delta + (Controller.Horn.IndexScanCold.program width clauses).size]? = some (.push 7)

private structure SourceCallerSeedSections (width n : Nat) (resident : Program width 8)
    (delta conflict : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Prop where
  setupAt : ∀ phase : Fin 9,
    resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 1) + phase.val]? =
    (Controller.Horn.WorklistSeed.coldSetupCode (n := n) width (Controller.Horn.SourceSerialize.base clauses)
      (Controller.Horn.IndexScanCold.recordStart width clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10))[phase.val]?
  seedAt : Controller.Horn.WorklistSeed.At (n := n) resident (Controller.Horn.SourceSerialize.base clauses)
    (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 10)
    (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict
  seedFits : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57 < 2 ^ width
  heapFits : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length + 3 * (clauses.map List.length).sum < 2 ^ width

private structure SourceCallerClassifierSections (width n : Nat) (resident : Program width 8)
    (delta conflict accept tag : Nat) (clauses : List (Controller.CNF.Clause (Fin n))) : Prop where
  fifoAt : ∀ phase : Fin 61,
    resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) + phase.val]? =
    (sourceDependencyRuntimeCode width n (Controller.Horn.SourceSerialize.base clauses)
      (delta + (Controller.Horn.IndexScanCold.program width clauses).size + 57) conflict)[phase.val]?
  fifoFits : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118 < 2 ^ width
  cycleAt : ∀ phase : Fin 8,
    resident[(delta + (Controller.Horn.IndexScanCold.program width clauses).size + 118) + phase.val]? =
    (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := n) (Controller.Horn.SourceSerialize.base clauses))
      (Controller.Horn.WorklistMark.queueStart (n := n) (Controller.Horn.SourceSerialize.base clauses) + n) accept tag)[phase.val]?
  cycleFits : delta + (Controller.Horn.IndexScanCold.program width clauses).size + 126 < 2 ^ width


private structure SourceCallerSuffixSections (width channels n : Nat) (resident : Program width 8)
    (entry delta conflict accept tag rankDone rawWords typedWords : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) (copied : Program width 8) : Prop where
  rankFits : accept + 1 + 2 * rawWords + 2 * n + 19 < 2 ^ width
  rankRoom : Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
    3 * (clauses.map List.length).sum + rawWords + n < 2 ^ width
  popAt : resident[accept]? = some (.pop 4)
  reloadAt : ForestZeroCallerWiden.WidenedBlockAt resident (accept + 1) (InputLoad.code (width := width) rawWords)
  zeroAt : ForestZeroCallerWiden.WidenedBlockAt resident (accept + 1 + 2 * rawWords) (Initialize.code (word width 0) n)
  rankSetupAt : ∀ phase : Fin 11,
    resident[(accept + 1 + 2 * rawWords + 2 * n) + phase.val]? =
    (sourceRankSetupCode width n (Controller.Horn.SourceSerialize.base clauses) rawWords
      (accept + 1 + 2 * rawWords + 2 * n + 11))[phase.val]?
  rankAt : ∀ phase : Fin 8,
    resident[(accept + 1 + 2 * rawWords + 2 * n + 11) + phase.val]? =
    (RawAdapterProgram.rankCopyCode width (accept + 1 + 2 * rawWords + 2 * n + 11) rankDone)[phase.val]?
  copyAt : ∀ phase : Fin copied.size, resident[rankDone + phase.val]? = copied[phase.val]?
  copyFits : rankDone + copied.size < 2 ^ width
  copyRoom : channels + (Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
    3 * (clauses.map List.length).sum + rawWords + n) + typedWords < 2 ^ width


private theorem source_caller_transfer_sections (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (codeFits : entry + (sourceCallerCode raw valid entry tag).size < 2 ^ rawExecutionWidth channels raw)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let V := raw.nodes.size
  let delta := entry + 97
  SourceCallerTransferSections width V resident entry delta clauses := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let V := raw.nodes.size
  let delta := entry + 97
  have transferPhysical : ∀ phase : Fin 97, resident[entry + phase.val]? =
      (sourceZeroTransferCode width entry delta)[phase.val]? := by
    intro phase
    have selected := source_caller_transfer_part raw valid resident entry tag physical phase
    change resident[(entry + 0) + phase.val]? = (sourceZeroTransferCode width entry delta)[phase.val]? at selected
    simpa only [Nat.add_zero] using selected
  have transferAt := source_transfer_fixed_section resident entry delta transferPhysical
  have coldPart := source_caller_cold_part raw valid resident entry tag physical
  have pushPart := source_caller_push_part raw valid resident entry tag physical
  have coldAt : sourceRelocatedCodeAt resident cold delta := by
    apply source_relocated_section
    intro phase
    have selected := coldPart phase
    change resident[delta + phase.val]? =
      (cold.map (RawAdapterProgram.relocatedInstruction delta))[phase.val]? at selected
    exact selected
  have pushAt : resident[delta + cold.size]? = some (.push 7) := by
    have selected := pushPart ⟨0, by decide⟩
    change resident[(entry + (97 + cold.size)) + 0]? = some (.push 7) at selected
    simpa only [delta, Nat.add_assoc, Nat.add_zero] using selected
  refine ⟨?_, transferAt, coldAt, pushAt⟩
  rw [source_caller_code_size] at codeFits
  change entry + 97 < 2 ^ rawExecutionWidth channels raw
  omega

private theorem source_caller_seed_sections (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (codeFits : entry + (sourceCallerCode raw valid entry tag).size < 2 ^ rawExecutionWidth channels raw)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  SourceCallerSeedSections width V resident delta conflict clauses := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  have dimensions := source_dependency_dimensions raw valid
  have coldSize : cold.size = 231 + 12 * V + 6 * (rowChildren (originalRows raw)).length := by
    simp only [cold, clauses, Controller.Horn.IndexScanCold.program_size,
      Controller.Horn.IndexScanCold.entry, Controller.Horn.NormalizeCold.program_size,
      dimensions.1, dimensions.2, V]
    omega
  have setupPart := source_caller_setup_part raw valid resident entry tag physical
  have seedPart := source_caller_seed_part raw valid resident entry tag physical
  have setupAt : ∀ phase : Fin 9, resident[(delta + cold.size + 1) + phase.val]? =
      (Controller.Horn.WorklistSeed.coldSetupCode (n := V) width base
        (Controller.Horn.IndexScanCold.recordStart width clauses) (delta + cold.size + 10))[phase.val]? := by
    intro phase
    have selected := setupPart phase
    have address : (entry + (97 + cold.size + 1)) + phase.val =
        (delta + cold.size + 1) + phase.val := by dsimp only [delta]; omega
    rw [address] at selected
    exact selected
  have seedAt : Controller.Horn.WorklistSeed.At (n := V) resident base
      (delta + cold.size + 10) (delta + cold.size + 57) conflict := by
    apply source_seed_fixed_section
    intro phase
    have selected := seedPart phase
    have address : (entry + (97 + cold.size + 1 + 9)) + phase.val =
        (delta + cold.size + 10) + phase.val := by dsimp only [delta]; omega
    rw [address] at selected
    exact selected
  have rooms := source_heap_rooms raw valid
  refine ⟨setupAt, seedAt, ?_, rooms.1⟩
  change delta + cold.size + 57 < 2 ^ width
  rw [coldSize]
  rw [source_caller_code_size] at codeFits
  dsimp only [delta, width, V] at codeFits ⊢
  omega

private theorem source_caller_classifier_sections (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (codeFits : entry + (sourceCallerCode raw valid entry tag).size < 2 ^ rawExecutionWidth channels raw)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  SourceCallerClassifierSections width V resident delta conflict accept tag clauses := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  have dimensions := source_dependency_dimensions raw valid
  have coldSize : cold.size = 231 + 12 * V + 6 * (rowChildren (originalRows raw)).length := by
    simp only [cold, clauses, Controller.Horn.IndexScanCold.program_size,
      Controller.Horn.IndexScanCold.entry, Controller.Horn.NormalizeCold.program_size,
      dimensions.1, dimensions.2, V]
    omega
  have fifoPart := source_caller_fifo_part raw valid resident entry tag physical
  have cyclePart := source_caller_cycle_part raw valid resident entry tag physical
  have fifoAt : ∀ phase : Fin 61, resident[(delta + cold.size + 57) + phase.val]? =
      (sourceDependencyRuntimeCode width V base (delta + cold.size + 57) conflict)[phase.val]? := by
    intro phase
    have selected := fifoPart phase
    have address : (entry + (97 + cold.size + 1 + 9 + 47)) + phase.val =
        (delta + cold.size + 57) + phase.val := by dsimp only [delta]; omega
    rw [address] at selected
    exact selected
  have cycleAt : ∀ phase : Fin 8, resident[(delta + cold.size + 118) + phase.val]? =
      (sourceCycleCode width (Controller.Horn.WorklistBucketReady.tailSlot (n := V) base)
        (Controller.Horn.WorklistMark.queueStart (n := V) base + V) accept tag)[phase.val]? := by
    intro phase
    have selected := cyclePart phase
    have address : (entry + (97 + cold.size + 1 + 9 + 47 + 61)) + phase.val =
        (delta + cold.size + 118) + phase.val := by dsimp only [delta]; omega
    rw [address] at selected
    exact selected
  have rooms := source_heap_rooms raw valid
  refine ⟨fifoAt, ?_, cycleAt, ?_⟩
  · change delta + cold.size + 118 < 2 ^ width
    rw [coldSize]
    rw [source_caller_code_size] at codeFits
    dsimp only [delta, width, V] at codeFits ⊢
    omega
  · change delta + cold.size + 126 < 2 ^ width
    rw [coldSize]
    rw [source_caller_code_size] at codeFits
    dsimp only [delta, width, V] at codeFits ⊢
    omega

private theorem source_caller_prefix_sections (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (codeFits : entry + (sourceCallerCode raw valid entry tag).size < 2 ^ rawExecutionWidth channels raw)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  SourceCallerPrefixSections width channels V resident entry delta conflict accept tag rankDone W
    (5 + 6 * V + (rowChildren (originalRows raw)).length + (rowGuards (originalRows raw)).length + raw.roots.length)
    clauses copied := by
  have transfer := source_caller_transfer_sections raw valid resident entry tag codeFits physical
  have seed := source_caller_seed_sections raw valid resident entry tag codeFits physical
  have classifier := source_caller_classifier_sections raw valid resident entry tag codeFits physical
  exact ⟨transfer.transferFits, transfer.transferAt, transfer.coldAt, transfer.pushAt,
    seed.setupAt, seed.seedAt, seed.seedFits, seed.heapFits,
    classifier.fifoAt, classifier.fifoFits, classifier.cycleAt, classifier.cycleFits⟩

private theorem source_caller_suffix_sections (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (codeFits : entry + (sourceCallerCode raw valid entry tag).size < 2 ^ rawExecutionWidth channels raw)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  SourceCallerSuffixSections width channels V resident entry delta conflict accept tag rankDone W
    (5 + 6 * V + (rowChildren (originalRows raw)).length + (rowGuards (originalRows raw)).length + raw.roots.length)
    clauses copied := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  have dimensions := source_dependency_dimensions raw valid
  have coldSize : cold.size = 231 + 12 * V + 6 * (rowChildren (originalRows raw)).length := by
    simp only [cold, clauses, Controller.Horn.IndexScanCold.program_size,
      Controller.Horn.IndexScanCold.entry, Controller.Horn.NormalizeCold.program_size,
      dimensions.1, dimensions.2, V]
    omega
  have Wsize : W = 9 + 6 * V + (rowChildren (originalRows raw)).length +
      (rowGuards (originalRows raw)).length + raw.roots.length := by
    simp only [W, original_packet_size, V]
  have copiedSize : copied.size = 713 + 6 * channels + 6 * V := by
    simp only [copied, typedCopyColdCode_size, typed_shape_code_size]
    omega
  have wholeSize : (sourceCallerCode raw valid entry tag).size =
      246 + cold.size + 2 * W + 2 * V + copied.size := by
    rw [source_caller_code_size, coldSize, Wsize, copiedSize]
    dsimp only [V]
    omega
  have popPart := source_caller_pop_part raw valid resident entry tag physical
  have reloadPart := source_caller_reload_part raw valid resident entry tag physical
  have zeroPart := source_caller_zero_part raw valid resident entry tag physical
  have rankSetupPart := source_caller_rankSetup_part raw valid resident entry tag physical
  have rankPart := source_caller_rank_part raw valid resident entry tag physical
  have copyPart := source_caller_copy_part raw valid resident entry tag physical
  have popAt : resident[accept]? = some (.pop 4) := by
    have selected := popPart ⟨0, by decide⟩
    change resident[(entry + (97 + cold.size + 1 + 9 + 47 + 61 + 8)) + 0]? = some (.pop 4) at selected
    simpa only [accept, delta, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero] using selected
  have reloadAt : ForestZeroCallerWiden.WidenedBlockAt resident (accept + 1)
      (InputLoad.code (width := width) W) := by
    apply source_widened_section
    intro phase
    have inside : phase.val < 2 * W := by
      simpa only [widenProgram, Array.size_map, List.size_toArray, InputLoad.code_length] using phase.isLt
    simpa only [accept, delta, Nat.add_assoc, Nat.reduceAdd] using reloadPart ⟨phase.val, inside⟩
  have zeroAt : ForestZeroCallerWiden.WidenedBlockAt resident (accept + 1 + 2 * W)
      (Initialize.code (word width 0) V) := by
    apply source_widened_section
    intro phase
    have inside : phase.val < 2 * V := by
      simpa only [widenProgram, Array.size_map, List.size_toArray, Initialize.code_length] using phase.isLt
    simpa only [accept, delta, Nat.add_assoc, Nat.reduceAdd] using zeroPart ⟨phase.val, inside⟩
  have rankSetupAt : ∀ phase : Fin 11,
      resident[(accept + 1 + 2 * W + 2 * V) + phase.val]? =
        (sourceRankSetupCode width V base W rankEntry)[phase.val]? := by
    intro phase
    have selected := rankSetupPart phase
    have address : (entry + (97 + cold.size + 1 + 9 + 47 + 61 + 8 + 1 + 2 * W + 2 * V)) + phase.val =
        (accept + 1 + 2 * W + 2 * V) + phase.val := by dsimp only [accept, delta]; omega
    rw [address] at selected
    exact selected
  have rankAt : ∀ phase : Fin 8, resident[rankEntry + phase.val]? =
      (RawAdapterProgram.rankCopyCode width rankEntry rankDone)[phase.val]? := by
    intro phase
    have selected := rankPart phase
    have address : (entry + (97 + cold.size + 1 + 9 + 47 + 61 + 8 + 1 + 2 * W + 2 * V + 11)) + phase.val =
        rankEntry + phase.val := by dsimp only [rankEntry, accept, delta]; omega
    rw [address] at selected
    exact selected
  have copyAt : ∀ phase : Fin copied.size, resident[rankDone + phase.val]? = copied[phase.val]? := by
    intro phase
    have selected := copyPart phase
    have address : (entry + (97 + cold.size + 1 + 9 + 47 + 61 + 8 + 1 + 2 * W + 2 * V + 11 + 8)) + phase.val =
        rankDone + phase.val := by dsimp only [rankDone, rankEntry, accept, delta]; omega
    rw [address] at selected
    exact selected
  have rooms := source_heap_rooms raw valid
  have codeBound : entry + 246 + cold.size + 2 * W + 2 * V + copied.size < 2 ^ width := by
    have bound := codeFits
    rw [wholeSize] at bound
    simpa only [Nat.add_assoc, width] using bound
  have rankScalar : rankDone = entry + 243 + cold.size + 2 * W + 2 * V := by
    dsimp only [rankDone, rankEntry, accept, delta]
    omega
  refine ⟨?_, rooms.2.1, popAt, reloadAt, zeroAt, rankSetupAt, rankAt, copyAt, ?_, ?_⟩
  · change accept + 1 + 2 * W + 2 * V + 19 < 2 ^ width
    dsimp only [accept, delta]
    omega
  · change rankDone + copied.size < 2 ^ width
    rw [rankScalar]
    omega
  · have copiedRoom := rooms.2.2
    change channels + (Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum) + W + V +
      (5 + 6 * V + (rowChildren (originalRows raw)).length +
        (rowGuards (originalRows raw)).length + raw.roots.length) < 2 ^ width at copiedRoom
    change channels + (Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
      3 * (clauses.map List.length).sum + W + V) +
      (5 + 6 * V + (rowChildren (originalRows raw)).length +
        (rowGuards (originalRows raw)).length + raw.roots.length) < 2 ^ width
    omega

private theorem source_caller_sections (raw : RawDAG) (valid : raw.WellFormed channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (codeFits : entry + (sourceCallerCode raw valid entry tag).size < 2 ^ rawExecutionWidth channels raw)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  SourceCallerSections width channels V resident entry delta conflict accept tag rankDone W
    (5 + 6 * V + (rowChildren (originalRows raw)).length + (rowGuards (originalRows raw)).length + raw.roots.length)
    clauses copied := by
  have first := source_caller_prefix_sections raw valid resident entry tag codeFits physical
  have last := source_caller_suffix_sections raw valid resident entry tag codeFits physical
  exact ⟨first.transferFits, first.transferAt, first.coldAt, first.pushAt, first.setupAt, first.seedAt, first.seedFits, first.heapFits, first.fifoAt, first.fifoFits, first.cycleAt, first.cycleFits, last.rankFits, last.rankRoom, last.popAt, last.reloadAt, last.zeroAt, last.rankSetupAt, last.rankAt, last.copyAt, last.copyFits, last.copyRoom⟩

/-- The resident caller's physical sections execute the complete source runtime. -/
private theorem source_caller_runtime_execution (raw : RawDAG) (valid : raw.WellFormed channels)
    (assignment : Assignment channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (state : State (rawExecutionWidth channels raw) 8)
    (suffix : List (Word (rawExecutionWidth channels raw)))
    (image : OriginalImageStored state.heap 0 channels raw)
    (originalSize : state.heap.size = (originalPacket (rawExecutionWidth channels raw) channels raw).size)
    (input : state.stack = (originalPacket (rawExecutionWidth channels raw) channels raw).toList ++
      (List.ofFn (fun channel => boolWord (rawExecutionWidth channels raw) (assignment channel)) ++ suffix))
    (position : state.pc = word (rawExecutionWidth channels raw) entry)
    (running : state.halted = false)
    (codeFits : entry + (sourceCallerCode raw valid entry tag).size < 2 ^ rawExecutionWidth channels raw)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
    ((raw.toUnordered valid).Acyclic ∧
      ∃ numbering : (raw.toUnordered valid).Numbering,
        ∃ final ticks peak, Execution resident state final ticks peak ∧
          ticks ≤ sourceTransferTicks (rawExecutionWidth channels raw) channels raw + 61 * raw.nodes.size + 115 * ((RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).map List.length).sum + 131 * (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).length +
            2 * (originalPacket (rawExecutionWidth channels raw) channels raw).size +
            321 * numbering.toDAG.countedSize +
            4 * (Controller.Horn.IndexScanCold.recordStart (rawExecutionWidth channels raw) (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)) +
              3 * (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).length + 3 * ((RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).map List.length).sum +
              (originalPacket (rawExecutionWidth channels raw) channels raw).size + raw.nodes.size) +
            226 * (numbering.toDAG.roots.map (typedConeIncidenceSize numbering.toDAG)).sum + 305 ∧
          peak ≤ max (state.liveWords + 3 * dependencyPacketLength raw + 6 * raw.nodes.size + 6 +
              3 * (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).length + 3 * ((RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).map List.length).sum +
              2 * (numberedPacketWords (width := rawExecutionWidth channels raw) raw valid numbering).length)
            (38 * numbering.toDAG.countedSize + 1884 + suffix.length + state.output.length) ∧
          final.stack = suffix ∧
          final.output = (numbering.toDAG.roots.map (fun node =>
            boolWord (rawExecutionWidth channels raw) (numbering.toDAG.eval assignment node))).reverse ++
            state.output ∧ final.halted = true) ∨
    (¬(raw.toUnordered valid).Acyclic ∧ ∃ final ticks peak,
      Execution resident state final ticks peak ∧
      ticks ≤ sourceTransferTicks (rawExecutionWidth channels raw) channels raw + 51 * raw.nodes.size + 115 * ((RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).map List.length).sum + 131 * (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).length + 98 ∧
      peak ≤ state.liveWords + 3 * dependencyPacketLength raw + 5 * raw.nodes.size + 6 +
        3 * (RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).length + 3 * ((RawDependencyOrder.dependencyClauses (raw.toUnordered valid)).map List.length).sum ∧
      final.output = word (rawExecutionWidth channels raw) tag :: state.output ∧ final.halted = true) := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let cold := Controller.Horn.IndexScanCold.program width clauses
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  let base := Controller.Horn.SourceSerialize.base clauses
  let delta := entry + 97
  let accept := delta + cold.size + 126
  let rankEntry := accept + 1 + 2 * W + 2 * V + 11
  let rankDone := rankEntry + 8
  let copied := typedCopyColdCode width channels V
    (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
    raw.roots.length base rankDone
  let conflict := rankDone + copied.size
  have sections : SourceCallerSections width channels (raw.toUnordered valid).nodeCount resident
      entry delta conflict accept tag rankDone W
      (5 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
        (rowGuards (originalRows raw)).length + raw.roots.length) clauses copied :=
    source_caller_sections raw valid resident entry tag codeFits physical
  exact source_zero_runtime_from_block raw valid assignment clauses rfl
    resident delta conflict state suffix entry image originalSize input position running
    sections.transferFits sections.transferAt sections.coldAt sections.pushAt sections.setupAt sections.seedAt
    sections.seedFits sections.heapFits sections.fifoAt sections.fifoFits accept tag sections.cycleAt
    sections.cycleFits rankDone
    (by simpa only [Array.length_toList] using sections.rankFits)
    (by simpa only [Array.length_toList] using sections.rankRoom)
    sections.popAt (by simpa only [Array.length_toList] using sections.reloadAt)
    (by simpa only [Array.length_toList] using sections.zeroAt)
    (by simpa only [Array.length_toList] using sections.rankSetupAt)
    (by simpa only [Array.length_toList] using sections.rankAt) sections.copyAt sections.copyFits
    (by
      have room := sections.copyRoom
      change channels + (Controller.Horn.IndexScanCold.recordStart width clauses + 3 * clauses.length +
        3 * (clauses.map List.length).sum + W + raw.nodes.size) +
        (5 + 6 * raw.nodes.size + (rowChildren (originalRows raw)).length +
          (rowGuards (originalRows raw)).length + raw.roots.length) < 2 ^ width at room
      simpa only [width, W, Nat.add_assoc] using room)

/-- The assembled resident adapter executes every original source stage on one
machine trace. Its initial packet and saved copy are the running endpoint of
original-input validation and normalization. -/
theorem source_caller_execution (raw : RawDAG) (valid : raw.WellFormed channels)
    (assignment : Assignment channels)
    (resident : Program (rawExecutionWidth channels raw) 8) (entry tag : Nat)
    (state : State (rawExecutionWidth channels raw) 8)
    (suffix : List (Word (rawExecutionWidth channels raw)))
    (image : OriginalImageStored state.heap 0 channels raw)
    (originalSize : state.heap.size = (originalPacket (rawExecutionWidth channels raw) channels raw).size)
    (input : state.stack = (originalPacket (rawExecutionWidth channels raw) channels raw).toList ++
      (List.ofFn (fun channel => boolWord (rawExecutionWidth channels raw) (assignment channel)) ++ suffix))
    (position : state.pc = word (rawExecutionWidth channels raw) entry)
    (running : state.halted = false)
    (codeFits : entry + (sourceCallerCode raw valid entry tag).size < 2 ^ rawExecutionWidth channels raw)
    (physical : ∀ phase : Fin (sourceCallerCode raw valid entry tag).size,
      resident[entry + phase.val]? = (sourceCallerCode raw valid entry tag)[phase.val]?) :
    ((raw.toUnordered valid).Acyclic ∧ ∃ numbering : (raw.toUnordered valid).Numbering,
      ∃ final ticks peak, Execution resident state final ticks peak ∧
        ticks ≤ 814 * (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
          (rowGuards (originalRows raw)).length + raw.roots.length) + 544 +
            226 * (numbering.toDAG.roots.map (typedConeIncidenceSize numbering.toDAG)).sum ∧
        peak + programWords (sourceCallerCode raw valid entry tag) ≤
          6716 * (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
            (rowGuards (originalRows raw)).length + raw.roots.length + 1) +
              suffix.length + state.output.length ∧
        final.stack = suffix ∧
        final.output = (numbering.toDAG.roots.map (fun node =>
          boolWord (rawExecutionWidth channels raw) (numbering.toDAG.eval assignment node))).reverse ++ state.output ∧
        final.halted = true) ∨
    (¬(raw.toUnordered valid).Acyclic ∧ ∃ final ticks peak,
      Execution resident state final ticks peak ∧
        ticks ≤ 383 * (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
          (rowGuards (originalRows raw)).length + raw.roots.length + 1) ∧
        peak + programWords (sourceCallerCode raw valid entry tag) ≤
          6716 * (channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
            (rowGuards (originalRows raw)).length + raw.roots.length + 1) +
              suffix.length + state.output.length ∧
        final.output = word (rawExecutionWidth channels raw) tag :: state.output ∧ final.halted = true) := by
  let width := rawExecutionWidth channels raw
  let clauses := RawDependencyOrder.dependencyClauses (raw.toUnordered valid)
  let W := (originalPacket width channels raw).size
  let V := raw.nodes.size
  have dimensions := source_dependency_dimensions raw valid
  have Wsize : W = 9 + 6 * V + (rowChildren (originalRows raw)).length +
      (rowGuards (originalRows raw)).length + raw.roots.length := by
    simp only [W, original_packet_size, V]
  have continuation := source_caller_runtime_execution raw valid assignment resident entry tag
    state suffix image originalSize input position running codeFits physical
  have initialLive : state.liveWords = 2 * W + channels + suffix.length + state.output.length + 9 := by
    have heapCount : state.heap.size = W := originalSize
    have stackCount : state.stack.length = W + channels + suffix.length := by
      rw [input]
      simp only [List.length_append, Array.length_toList, List.length_ofFn]
      change W + (channels + suffix.length) = W + channels + suffix.length
      omega
    change 8 + state.heap.size + state.stack.length + state.output.length + 1 = _
    rw [heapCount, stackCount]
    omega
  have instructionWords : programWords (sourceCallerCode raw valid entry tag) =
      4 * (1208 + 6 * channels + 32 * V + 8 * (rowChildren (originalRows raw)).length +
        2 * (rowGuards (originalRows raw)).length + 2 * raw.roots.length) := by
    rw [programWords, source_caller_code_size]
  rcases continuation with accepted | rejected
  · rcases accepted with ⟨acyclic, numbering, final, ticks, peak, trace, time, space,
      stack, output, halted⟩
    have counted := source_numbered_size raw valid numbering
    have packetLength := numbered_packet_length (width := width) raw valid numbering
    simp only [clauses, source_transfer_ticks_exact, source_record_start_exact,
      original_packet_size, dependencyPacketLength, dimensions.1, dimensions.2, counted, packetLength] at time space
    rw [initialLive, Wsize] at space
    refine Or.inl ⟨acyclic, numbering, final, ticks, peak, trace, ?_, ?_, stack, output, halted⟩
    · omega
    · rw [instructionWords]
      omega
  · rcases rejected with ⟨cyclic, final, ticks, peak, trace, time, space, output, halted⟩
    simp only [clauses, source_transfer_ticks_exact, dependencyPacketLength, dimensions.1, dimensions.2] at time space
    rw [initialLive, Wsize] at space
    refine Or.inr ⟨cyclic, final, ticks, peak, trace, ?_, ?_, output, halted⟩
    · omega
    · rw [instructionWords]
      omega


/-- A fixed counted loader consumes the first stack packet into fresh heap cells. -/
def countedOriginalLoadCode (width entry done : Nat) : Program width 8 :=
  #[.branchZero 0 (word width done), .pop 5, .allocate 5,
    .add 0 0 7, .branchZero 6 (word width entry)]

/-- The temporary base is a register produced by the original input constructor.
Header loads derive packet length and the ending heap address. -/
def originalNormalizationSetupCode (width saveEntry : Nat) : Program width 8 :=
  #[.constant 6 (word width 0), .constant 7 (word width (2 ^ width - 1)),
    .copy 1 3, .load 4 1, .add 4 4 4, .copy 0 4, .add 4 4 4, .add 4 4 0,
    .constant 0 (word width 9), .add 4 4 0,
    .constant 0 (word width 2), .add 1 3 0, .load 0 1, .add 4 4 0,
    .constant 5 (word width 1), .add 1 1 5, .load 0 1, .add 4 4 0,
    .add 1 1 5, .load 0 1, .add 4 4 0,
    .add 2 3 4, .copy 0 4, .add 1 3 4, .add 1 1 7,
    .branchZero 6 (word width saveEntry)]

/-- Executed rearming preserves the physical packet, the saved heap count in
register two, the temporary base in register three, and packet length in four. -/
def originalSaveRearmCode (width saveEntry : Nat) : Program width 8 :=
  #[.copy 0 4, .add 1 3 4, .add 1 1 7, .branchZero 6 (word width saveEntry)]

def originalReleaseRearmCode (width releaseEntry : Nat) : Program width 8 :=
  #[.copy 0 2, .branchZero 6 (word width releaseEntry)]

def originalLoadRearmCode (width loadEntry : Nat) : Program width 8 :=
  #[.copy 0 4, .branchZero 6 (word width loadEntry)]

/-- A positive-base packet is physically copied twice, the temporary heap is
released, and one copy is reloaded at zero for the resident source caller. -/
def originalNormalizationCode (width entry callerEntry : Nat) : Program width 8 :=
  originalNormalizationSetupCode width (entry + 26) ++
    RawTransferLoops.reverseSaveCode width (entry + 26) (entry + 32) ++
    originalSaveRearmCode width (entry + 36) ++
    RawTransferLoops.reverseSaveCode width (entry + 36) (entry + 42) ++
    originalReleaseRearmCode width (entry + 44) ++
    RawTransferLoops.countedReleaseCode width (entry + 44) (entry + 48) ++
    originalLoadRearmCode width (entry + 50) ++
    countedOriginalLoadCode width (entry + 50) callerEntry

@[simp] theorem counted_original_load_code_size (width entry done : Nat) :
    (countedOriginalLoadCode width entry done).size = 5 := rfl

@[simp] theorem original_normalization_setup_code_size (width saveEntry : Nat) :
    (originalNormalizationSetupCode width saveEntry).size = 26 := rfl

@[simp] theorem original_save_rearm_code_size (width done : Nat) :
    (originalSaveRearmCode width done).size = 4 := rfl

@[simp] theorem original_release_rearm_code_size (width done : Nat) :
    (originalReleaseRearmCode width done).size = 2 := rfl

@[simp] theorem original_load_rearm_code_size (width done : Nat) :
    (originalLoadRearmCode width done).size = 2 := rfl

theorem counted_original_load_zero_step (resident : Program width 8)
    (entry done : Nat) (state : State width 8)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (running : state.halted = false) (zero : (state.reg 0).val = 0)
    (physical : RawTransferLoops.CodeAt resident entry (countedOriginalLoadCode width entry done)) :
    programStep resident state = some { state.advance with pc := word width done } := by
  have selected : resident[entry]? = some (.branchZero 0 (word width done)) := by
    simpa [countedOriginalLoadCode] using physical ⟨0, by simp [countedOriginalLoadCode]⟩
  rw [RawTransferLoops.fetched resident state entry _ position fits selected]
  simp only [step, running, Bool.false_eq_true, ↓reduceIte, zero]


private theorem counted_original_load_round (resident : Program width 8)
    (entry done count : Nat) (state : State width 8) (value : Word width)
    (suffix : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 5 < 2 ^ width) (countFits : count + 1 < 2 ^ width)
    (countReg : state.reg 0 = word width (count + 1))
    (maskReg : state.reg 7 = word width (2 ^ width - 1))
    (zeroReg : state.reg 6 = word width 0)
    (stack : state.stack = value :: suffix) (heapRoom : state.heap.size < 2 ^ width)
    (physical : RawTransferLoops.CodeAt resident entry (countedOriginalLoadCode width entry done)) :
    ∃ middle, Execution resident state middle 5 state.liveWords ∧
      middle.pc = word width entry ∧ middle.halted = false ∧
      middle.heap = state.heap.push value ∧ middle.stack = suffix ∧
      middle.output = state.output ∧ middle.reg 0 = word width count ∧
      middle.liveWords = state.liveWords ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 5 → middle.reg index = state.reg index) := by
  let s1 := state.advance
  let s2 := { s1.advance.put 5 value with stack := suffix }
  let s3 := { s2.advance with heap := state.heap.push value }
  let s4 := s3.advance.put 0 (word width count)
  let s5 := { s4.advance with pc := word width entry }
  have nz : (state.reg 0).val ≠ 0 := by
    rw [countReg]; simp only [word, Nat.mod_eq_of_lt countFits]; omega
  have p1 : s1.pc = word width (entry + 1) := RawTransferLoops.advance_position state position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc] using RawTransferLoops.advance_position s1 p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc] using RawTransferLoops.advance_position s2 p2 (by omega)
  have p4 : s4.pc = word width (entry + 4) := by
    change s3.advance.pc = _
    simpa only [Nat.add_assoc] using RawTransferLoops.advance_position s3 p3 (by omega)
  have t0 : programStep resident state = some s1 := by
    have selected := physical ⟨0, by simp [countedOriginalLoadCode]⟩
    have cell : resident[entry]? = some (.branchZero 0 (word width done)) := by
      simpa [countedOriginalLoadCode] using selected
    rw [RawTransferLoops.fetched resident state entry _ position (by omega) cell]
    simp only [step, running, Bool.false_eq_true, ↓reduceIte, nz, s1]
  have t1 : programStep resident s1 = some s2 := by
    have cell : resident[entry + 1]? = some (.pop 5) := by
      simpa [countedOriginalLoadCode] using physical ⟨1, by simp [countedOriginalLoadCode]⟩
    rw [RawTransferLoops.fetched resident s1 (entry + 1) _ p1 (by omega) cell]
    simp only [step, s1, State.advance, running, Bool.false_eq_true, ↓reduceIte, stack, s2]
  have t2 : programStep resident s2 = some s3 := by
    have cell : resident[entry + 2]? = some (.allocate 5) := by
      simpa [countedOriginalLoadCode] using physical ⟨2, by simp [countedOriginalLoadCode]⟩
    rw [RawTransferLoops.fetched resident s2 (entry + 2) _ p2 (by omega) cell]
    simp only [step, s2, s1, State.advance, State.put, ite_eq_left rfl, ite_true, ite_false,
      running, Bool.false_eq_true, ↓reduceIte, heapRoom, s3]
  have decrement : word width ((s3.reg 0).val + (s3.reg 7).val) = word width count := by
    have countValue : (word width (count + 1)).val = count + 1 := Nat.mod_eq_of_lt countFits
    have maskValue : (word width (2 ^ width - 1)).val = 2 ^ width - 1 :=
      Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)
    simpa only [s3, s2, s1, State.advance, State.put, ite_eq_right (by decide : (0 : Fin 8) ≠ 5),
      ite_eq_right (by decide : (7 : Fin 8) ≠ 5), countReg, maskReg, countValue, maskValue]
      using RawTransferLoops.decrement_word width count
  have t3 : programStep resident s3 = some s4 := by
    have cell : resident[entry + 3]? = some (.add 0 0 7) := by
      simpa [countedOriginalLoadCode] using physical ⟨3, by simp [countedOriginalLoadCode]⟩
    rw [RawTransferLoops.fetched resident s3 (entry + 3) _ p3 (by omega) cell]
    simp only [step, show s3.halted = false from running, Bool.false_eq_true, ↓reduceIte, decrement, s4]
  have t4 : programStep resident s4 = some s5 := by
    have cell : resident[entry + 4]? = some (.branchZero 6 (word width entry)) := by
      simpa [countedOriginalLoadCode] using physical ⟨4, by simp [countedOriginalLoadCode]⟩
    rw [RawTransferLoops.fetched resident s4 (entry + 4) _ p4 (by omega) cell]
    simp [step, s4, s3, s2, s1, State.advance, State.put, running, zeroReg, word, s5]
  have l1 : s1.liveWords = state.liveWords := rfl
  have l2 : s2.liveWords + 1 = state.liveWords := by
    simp only [State.liveWords, s2, s1, State.advance, State.put, stack, List.length_cons]
    omega
  have l3 : s3.liveWords = state.liveWords := by
    simp only [State.liveWords, s3, s2, s1, State.advance, State.put, stack,
      Array.size_push, List.length_cons]
    omega
  have l4 : s4.liveWords = state.liveWords := l3
  have l5 : s5.liveWords = state.liveWords := l4
  refine ⟨s5, ?_, rfl, running, rfl, rfl, rfl, ?_, l5, ?_⟩
  · simpa only [l1, l3, l4, l5, Nat.max_self, Nat.max_eq_right (by omega : s2.liveWords ≤ state.liveWords), Nat.reduceAdd]
      using Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3
        (Execution.cons t4 (Execution.refl s5)))))
  · simp [s5, s4, State.advance, State.put]
  · intro index n0 n5
    simp [s5, s4, s3, s2, s1, State.advance, State.put, n0, n5]


/-- A counted original packet reload uses one resident loop for every input size. -/
private theorem counted_original_load_execution (resident : Program width 8) (entry done : Nat)
    (values suffix : List (Word width)) :
    ∀ state : State width 8, state.pc = word width entry → state.halted = false →
      entry + 5 < 2 ^ width → values.length < 2 ^ width →
      state.reg 0 = word width values.length → state.reg 7 = word width (2 ^ width - 1) →
      state.reg 6 = word width 0 → state.stack = values ++ suffix →
      state.heap.size + values.length ≤ 2 ^ width →
      RawTransferLoops.CodeAt resident entry (countedOriginalLoadCode width entry done) →
    ∃ final peak, Execution resident state final (5 * values.length + 1) peak ∧
      peak ≤ state.liveWords ∧ final.heap = state.heap ++ values.toArray ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 0 = word width 0 ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 5 → final.reg index = state.reg index) := by
  induction values with
  | nil =>
    intro state position running room fits countReg maskReg zeroReg stack heapRoom physical
    let final := { state.advance with pc := word width done }
    have transition := counted_original_load_zero_step resident entry done state position (by omega)
      running (by rw [countReg]; simp [word]) physical
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, state.liveWords, ?_, le_rfl, ?_, ?_, rfl, rfl, running, countReg, ?_⟩
    · simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, live, Nat.max_self]
        using Execution.cons transition (Execution.refl final)
    · change state.heap = state.heap ++ #[]
      rw [Array.append_empty]
    · change state.stack = suffix
      simpa only [List.nil_append] using stack
    · intro index n0 n5; rfl
  | cons value values ih =>
    intro state position running room fits countReg maskReg zeroReg stack heapRoom physical
    obtain ⟨middle, first, middlePC, middleRunning, middleHeap, middleStack,
      middleOutput, middleCount, middleLive, middleFrame⟩ :=
      counted_original_load_round resident entry done values.length state value (values ++ suffix)
        position running room (by simpa only [List.length_cons] using fits)
        (by simpa only [List.length_cons] using countReg) maskReg zeroReg
        (by simpa only [List.cons_append] using stack)
        (by simp only [List.length_cons] at heapRoom; omega) physical
    obtain ⟨final, lastPeak, last, lastSpace, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalCount, finalFrame⟩ :=
      ih middle middlePC middleRunning room (by simp only [List.length_cons] at fits; omega)
        middleCount ((middleFrame 7 (by decide) (by decide)).trans maskReg)
        ((middleFrame 6 (by decide) (by decide)).trans zeroReg) middleStack
        (by rw [middleHeap]; simp only [Array.size_push, List.length_cons] at heapRoom ⊢; omega) physical
    refine ⟨final, max state.liveWords lastPeak, ?_, Nat.max_le.mpr
      ⟨le_rfl, lastSpace.trans (Nat.le_of_eq middleLive)⟩, ?_, finalStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, finalCount, ?_⟩
    · have composed := Execution.append first last
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using composed
    · rw [finalHeap, middleHeap]
      have conversion : (value :: values).toArray = #[value] ++ values.toArray := by
        simpa only [List.cons_append, List.nil_append] using (List.append_toArray [value] values).symm
      rw [conversion, Array.push_eq_append, Array.append_assoc]
    · intro index n0 n5
      exact (finalFrame index n0 n5).trans (middleFrame index n0 n5)


private theorem original_normalization_setup_execution (resident : Program width 8)
    (entry saveEntry tempbase nodes children guards roots : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 26 < 2 ^ width) (positive : 0 < tempbase)
    (capacity : tempbase + (9 + 6 * nodes + children + guards + roots) < 2 ^ width)
    (baseReg : state.reg 3 = word width tempbase)
    (nodeCell : state.heap[tempbase]? = some (word width nodes))
    (rootCell : state.heap[tempbase + 2]? = some (word width roots))
    (childCell : state.heap[tempbase + 3]? = some (word width children))
    (guardCell : state.heap[tempbase + 4]? = some (word width guards))
    (physical : RawTransferLoops.CodeAt resident entry (originalNormalizationSetupCode width saveEntry)) :
    ∃ final, Execution resident state final 26 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width saveEntry ∧ final.halted = false ∧
      final.reg 0 = word width (9 + 6 * nodes + children + guards + roots) ∧
      final.reg 1 = word width (tempbase + (9 + 6 * nodes + children + guards + roots) - 1) ∧
      final.reg 2 = word width (tempbase + (9 + 6 * nodes + children + guards + roots)) ∧
      final.reg 3 = state.reg 3 ∧ final.reg 4 = word width (9 + 6 * nodes + children + guards + roots) ∧
      final.reg 6 = word width 0 ∧ final.reg 7 = word width (2 ^ width - 1) := by
  let s1 : State width 8 := { reg := copyRegisters (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (state.reg 7), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 1), halted := false }
  let s2 : State width 8 := { reg := copyRegisters (state.reg 0) (state.reg 1) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 2), halted := false }
  let s3 : State width 8 := { reg := copyRegisters (state.reg 0) (state.reg 3) (state.reg 2) (state.reg 3) (state.reg 4) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 3), halted := false }
  let s4 : State width 8 := { reg := copyRegisters (state.reg 0) (state.reg 3) (state.reg 2) (state.reg 3) (word width (nodes)) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 4), halted := false }
  let s5 : State width 8 := { reg := copyRegisters (state.reg 0) (state.reg 3) (state.reg 2) (state.reg 3) (word width ((nodes) + (nodes))) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 5), halted := false }
  let s6 : State width 8 := { reg := copyRegisters (word width ((nodes) + (nodes))) (state.reg 3) (state.reg 2) (state.reg 3) (word width ((nodes) + (nodes))) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 6), halted := false }
  let s7 : State width 8 := { reg := copyRegisters (word width ((nodes) + (nodes))) (state.reg 3) (state.reg 2) (state.reg 3) (word width (((nodes) + (nodes)) + ((nodes) + (nodes)))) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 7), halted := false }
  let s8 : State width 8 := { reg := copyRegisters (word width ((nodes) + (nodes))) (state.reg 3) (state.reg 2) (state.reg 3) (word width ((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes)))) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 8), halted := false }
  let s9 : State width 8 := { reg := copyRegisters (word width (9)) (state.reg 3) (state.reg 2) (state.reg 3) (word width ((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes)))) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 9), halted := false }
  let s10 : State width 8 := { reg := copyRegisters (word width (9)) (state.reg 3) (state.reg 2) (state.reg 3) (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9))) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 10), halted := false }
  let s11 : State width 8 := { reg := copyRegisters (word width (2)) (state.reg 3) (state.reg 2) (state.reg 3) (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9))) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 11), halted := false }
  let s12 : State width 8 := { reg := copyRegisters (word width (2)) (word width ((tempbase) + (2))) (state.reg 2) (state.reg 3) (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9))) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 12), halted := false }
  let s13 : State width 8 := { reg := copyRegisters (word width (roots)) (word width ((tempbase) + (2))) (state.reg 2) (state.reg 3) (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9))) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 13), halted := false }
  let s14 : State width 8 := { reg := copyRegisters (word width (roots)) (word width ((tempbase) + (2))) (state.reg 2) (state.reg 3) (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots))) (state.reg 5) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 14), halted := false }
  let s15 : State width 8 := { reg := copyRegisters (word width (roots)) (word width ((tempbase) + (2))) (state.reg 2) (state.reg 3) (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 15), halted := false }
  let s16 : State width 8 := { reg := copyRegisters (word width (roots)) (word width (((tempbase) + (2)) + (1))) (state.reg 2) (state.reg 3) (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 16), halted := false }
  let s17 : State width 8 := { reg := copyRegisters (word width (children)) (word width (((tempbase) + (2)) + (1))) (state.reg 2) (state.reg 3) (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 17), halted := false }
  let s18 : State width 8 := { reg := copyRegisters (word width (children)) (word width (((tempbase) + (2)) + (1))) (state.reg 2) (state.reg 3) (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 18), halted := false }
  let s19 : State width 8 := { reg := copyRegisters (word width (children)) (word width ((((tempbase) + (2)) + (1)) + (1))) (state.reg 2) (state.reg 3) (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 19), halted := false }
  let s20 : State width 8 := { reg := copyRegisters (word width (guards)) (word width ((((tempbase) + (2)) + (1)) + (1))) (state.reg 2) (state.reg 3) (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 20), halted := false }
  let s21 : State width 8 := { reg := copyRegisters (word width (guards)) (word width ((((tempbase) + (2)) + (1)) + (1))) (state.reg 2) (state.reg 3) (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 21), halted := false }
  let s22 : State width 8 := { reg := copyRegisters (word width (guards)) (word width ((((tempbase) + (2)) + (1)) + (1))) (word width ((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards)))) (state.reg 3) (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 22), halted := false }
  let s23 : State width 8 := { reg := copyRegisters (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) (word width ((((tempbase) + (2)) + (1)) + (1))) (word width ((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards)))) (state.reg 3) (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 23), halted := false }
  let s24 : State width 8 := { reg := copyRegisters (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) (word width ((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards)))) (word width ((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards)))) (state.reg 3) (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 24), halted := false }
  let s25 : State width 8 := { reg := copyRegisters (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) (word width (((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) + (2 ^ width - 1))) (word width ((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards)))) (state.reg 3) (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (entry + 25), halted := false }
  let s26 : State width 8 := { reg := copyRegisters (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) (word width (((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) + (2 ^ width - 1))) (word width ((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards)))) (state.reg 3) (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) (word width (1)) (word width (0)) (word width (2 ^ width - 1)), heap := state.heap, stack := state.stack, output := state.output, pc := word width (saveEntry), halted := false }
  have pc0 : state.pc = word width (entry + 0) := by simpa only [Nat.add_zero] using position
  have run1 : state.halted = false := running
  have e1 : state.advance.put 6 (word width (0)) = s1 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s1, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC state (entry + 0) pc0 (by omega)
    · exact running
  have t1 : programStep resident state = some s1 := by
    rw [fetched resident state (entry + 0) (.constant 6 (word width (0))) pc0 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨0, by change 0 < 26; decide⟩)]
    rw [← e1]
    exact copy_constant_step state 6 (word width (0)) run1
  have live1 : s1.liveWords = state.liveWords := rfl
  have pc1 : s1.pc = word width (entry + 1) := rfl
  have run2 : s1.halted = false := rfl
  have e2 : s1.advance.put 7 (word width (2 ^ width - 1)) = s2 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s2, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s1 (entry + 1) pc1 (by omega)
    · rfl
  have t2 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) (.constant 7 (word width (2 ^ width - 1))) pc1 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨1, by change 1 < 26; decide⟩)]
    rw [← e2]
    exact copy_constant_step s1 7 (word width (2 ^ width - 1)) run2
  have live2 : s2.liveWords = state.liveWords := rfl
  have pc2 : s2.pc = word width (entry + 2) := rfl
  have run3 : s2.halted = false := rfl
  have e3 : s2.advance.put 1 (state.reg 3) = s3 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s3, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s2 (entry + 2) pc2 (by omega)
    · rfl
  have t3 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) (.copy 1 3) pc2 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨2, by change 2 < 26; decide⟩)]
    rw [← e3]
    exact copy_copy_step s2 1 3 (state.reg 3) run3 (by simp [s2, copyRegisters])
  have live3 : s3.liveWords = state.liveWords := rfl
  have pc3 : s3.pc = word width (entry + 3) := rfl
  have run4 : s3.halted = false := rfl
  have e4 : s3.advance.put 4 (word width (nodes)) = s4 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s4, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s3 (entry + 3) pc3 (by omega)
    · rfl
  have t4 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) (.load 4 1) pc3 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨3, by change 3 < 26; decide⟩)]
    rw [← e4]
    exact copy_load_step s3 4 1 (tempbase) (word width (nodes)) run4 (by omega) (by simp [s3, copyRegisters, baseReg]) (by simpa only [s3] using nodeCell)
  have live4 : s4.liveWords = state.liveWords := rfl
  have pc4 : s4.pc = word width (entry + 4) := rfl
  have run5 : s4.halted = false := rfl
  have e5 : s4.advance.put 4 (word width ((nodes) + (nodes))) = s5 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s5, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s4 (entry + 4) pc4 (by omega)
    · rfl
  have t5 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) (.add 4 4 4) pc4 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨4, by change 4 < 26; decide⟩)]
    rw [← e5]
    exact copy_add_step s4 4 4 4 (nodes) (nodes) run5 (by omega) (by omega) (by simp [s4, copyRegisters, baseReg]) (by simp [s4, copyRegisters, baseReg])
  have live5 : s5.liveWords = state.liveWords := rfl
  have pc5 : s5.pc = word width (entry + 5) := rfl
  have run6 : s5.halted = false := rfl
  have e6 : s5.advance.put 0 (word width ((nodes) + (nodes))) = s6 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s6, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s5 (entry + 5) pc5 (by omega)
    · rfl
  have t6 : programStep resident s5 = some s6 := by
    rw [fetched resident s5 (entry + 5) (.copy 0 4) pc5 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨5, by change 5 < 26; decide⟩)]
    rw [← e6]
    exact copy_copy_step s5 0 4 (word width ((nodes) + (nodes))) run6 (by simp [s5, copyRegisters])
  have live6 : s6.liveWords = state.liveWords := rfl
  have pc6 : s6.pc = word width (entry + 6) := rfl
  have run7 : s6.halted = false := rfl
  have e7 : s6.advance.put 4 (word width (((nodes) + (nodes)) + ((nodes) + (nodes)))) = s7 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s7, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s6 (entry + 6) pc6 (by omega)
    · rfl
  have t7 : programStep resident s6 = some s7 := by
    rw [fetched resident s6 (entry + 6) (.add 4 4 4) pc6 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨6, by change 6 < 26; decide⟩)]
    rw [← e7]
    exact copy_add_step s6 4 4 4 ((nodes) + (nodes)) ((nodes) + (nodes)) run7 (by omega) (by omega) (by simp [s6, copyRegisters, baseReg]) (by simp [s6, copyRegisters, baseReg])
  have live7 : s7.liveWords = state.liveWords := rfl
  have pc7 : s7.pc = word width (entry + 7) := rfl
  have run8 : s7.halted = false := rfl
  have e8 : s7.advance.put 4 (word width ((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes)))) = s8 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s8, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s7 (entry + 7) pc7 (by omega)
    · rfl
  have t8 : programStep resident s7 = some s8 := by
    rw [fetched resident s7 (entry + 7) (.add 4 4 0) pc7 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨7, by change 7 < 26; decide⟩)]
    rw [← e8]
    exact copy_add_step s7 4 4 0 (((nodes) + (nodes)) + ((nodes) + (nodes))) ((nodes) + (nodes)) run8 (by omega) (by omega) (by simp [s7, copyRegisters, baseReg]) (by simp [s7, copyRegisters, baseReg])
  have live8 : s8.liveWords = state.liveWords := rfl
  have pc8 : s8.pc = word width (entry + 8) := rfl
  have run9 : s8.halted = false := rfl
  have e9 : s8.advance.put 0 (word width (9)) = s9 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s9, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s8 (entry + 8) pc8 (by omega)
    · rfl
  have t9 : programStep resident s8 = some s9 := by
    rw [fetched resident s8 (entry + 8) (.constant 0 (word width (9))) pc8 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨8, by change 8 < 26; decide⟩)]
    rw [← e9]
    exact copy_constant_step s8 0 (word width (9)) run9
  have live9 : s9.liveWords = state.liveWords := rfl
  have pc9 : s9.pc = word width (entry + 9) := rfl
  have run10 : s9.halted = false := rfl
  have e10 : s9.advance.put 4 (word width (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9))) = s10 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s10, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s9 (entry + 9) pc9 (by omega)
    · rfl
  have t10 : programStep resident s9 = some s10 := by
    rw [fetched resident s9 (entry + 9) (.add 4 4 0) pc9 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨9, by change 9 < 26; decide⟩)]
    rw [← e10]
    exact copy_add_step s9 4 4 0 ((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) (9) run10 (by omega) (by omega) (by simp [s9, copyRegisters, baseReg]) (by simp [s9, copyRegisters, baseReg])
  have live10 : s10.liveWords = state.liveWords := rfl
  have pc10 : s10.pc = word width (entry + 10) := rfl
  have run11 : s10.halted = false := rfl
  have e11 : s10.advance.put 0 (word width (2)) = s11 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s11, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s10 (entry + 10) pc10 (by omega)
    · rfl
  have t11 : programStep resident s10 = some s11 := by
    rw [fetched resident s10 (entry + 10) (.constant 0 (word width (2))) pc10 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨10, by change 10 < 26; decide⟩)]
    rw [← e11]
    exact copy_constant_step s10 0 (word width (2)) run11
  have live11 : s11.liveWords = state.liveWords := rfl
  have pc11 : s11.pc = word width (entry + 11) := rfl
  have run12 : s11.halted = false := rfl
  have e12 : s11.advance.put 1 (word width ((tempbase) + (2))) = s12 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s12, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s11 (entry + 11) pc11 (by omega)
    · rfl
  have t12 : programStep resident s11 = some s12 := by
    rw [fetched resident s11 (entry + 11) (.add 1 3 0) pc11 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨11, by change 11 < 26; decide⟩)]
    rw [← e12]
    exact copy_add_step s11 1 3 0 (tempbase) (2) run12 (by omega) (by omega) (by simp [s11, copyRegisters, baseReg]) (by simp [s11, copyRegisters, baseReg])
  have live12 : s12.liveWords = state.liveWords := rfl
  have pc12 : s12.pc = word width (entry + 12) := rfl
  have run13 : s12.halted = false := rfl
  have e13 : s12.advance.put 0 (word width (roots)) = s13 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s13, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s12 (entry + 12) pc12 (by omega)
    · rfl
  have t13 : programStep resident s12 = some s13 := by
    rw [fetched resident s12 (entry + 12) (.load 0 1) pc12 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨12, by change 12 < 26; decide⟩)]
    rw [← e13]
    exact copy_load_step s12 0 1 ((tempbase) + (2)) (word width (roots)) run13 (by omega) (by simp [s12, copyRegisters, baseReg]) (by simpa only [s12] using rootCell)
  have live13 : s13.liveWords = state.liveWords := rfl
  have pc13 : s13.pc = word width (entry + 13) := rfl
  have run14 : s13.halted = false := rfl
  have e14 : s13.advance.put 4 (word width ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots))) = s14 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s14, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s13 (entry + 13) pc13 (by omega)
    · rfl
  have t14 : programStep resident s13 = some s14 := by
    rw [fetched resident s13 (entry + 13) (.add 4 4 0) pc13 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨13, by change 13 < 26; decide⟩)]
    rw [← e14]
    exact copy_add_step s13 4 4 0 (((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) (roots) run14 (by omega) (by omega) (by simp [s13, copyRegisters, baseReg]) (by simp [s13, copyRegisters, baseReg])
  have live14 : s14.liveWords = state.liveWords := rfl
  have pc14 : s14.pc = word width (entry + 14) := rfl
  have run15 : s14.halted = false := rfl
  have e15 : s14.advance.put 5 (word width (1)) = s15 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s15, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s14 (entry + 14) pc14 (by omega)
    · rfl
  have t15 : programStep resident s14 = some s15 := by
    rw [fetched resident s14 (entry + 14) (.constant 5 (word width (1))) pc14 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨14, by change 14 < 26; decide⟩)]
    rw [← e15]
    exact copy_constant_step s14 5 (word width (1)) run15
  have live15 : s15.liveWords = state.liveWords := rfl
  have pc15 : s15.pc = word width (entry + 15) := rfl
  have run16 : s15.halted = false := rfl
  have e16 : s15.advance.put 1 (word width (((tempbase) + (2)) + (1))) = s16 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s16, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s15 (entry + 15) pc15 (by omega)
    · rfl
  have t16 : programStep resident s15 = some s16 := by
    rw [fetched resident s15 (entry + 15) (.add 1 1 5) pc15 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨15, by change 15 < 26; decide⟩)]
    rw [← e16]
    exact copy_add_step s15 1 1 5 ((tempbase) + (2)) (1) run16 (by omega) (by omega) (by simp [s15, copyRegisters, baseReg]) (by simp [s15, copyRegisters, baseReg])
  have live16 : s16.liveWords = state.liveWords := rfl
  have pc16 : s16.pc = word width (entry + 16) := rfl
  have run17 : s16.halted = false := rfl
  have e17 : s16.advance.put 0 (word width (children)) = s17 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s17, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s16 (entry + 16) pc16 (by omega)
    · rfl
  have t17 : programStep resident s16 = some s17 := by
    rw [fetched resident s16 (entry + 16) (.load 0 1) pc16 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨16, by change 16 < 26; decide⟩)]
    rw [← e17]
    exact copy_load_step s16 0 1 (((tempbase) + (2)) + (1)) (word width (children)) run17 (by omega) (by simp [s16, copyRegisters, baseReg]) (by simpa only [s16] using childCell)
  have live17 : s17.liveWords = state.liveWords := rfl
  have pc17 : s17.pc = word width (entry + 17) := rfl
  have run18 : s17.halted = false := rfl
  have e18 : s17.advance.put 4 (word width (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children))) = s18 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s18, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s17 (entry + 17) pc17 (by omega)
    · rfl
  have t18 : programStep resident s17 = some s18 := by
    rw [fetched resident s17 (entry + 17) (.add 4 4 0) pc17 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨17, by change 17 < 26; decide⟩)]
    rw [← e18]
    exact copy_add_step s17 4 4 0 ((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) (children) run18 (by omega) (by omega) (by simp [s17, copyRegisters, baseReg]) (by simp [s17, copyRegisters, baseReg])
  have live18 : s18.liveWords = state.liveWords := rfl
  have pc18 : s18.pc = word width (entry + 18) := rfl
  have run19 : s18.halted = false := rfl
  have e19 : s18.advance.put 1 (word width ((((tempbase) + (2)) + (1)) + (1))) = s19 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s19, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s18 (entry + 18) pc18 (by omega)
    · rfl
  have t19 : programStep resident s18 = some s19 := by
    rw [fetched resident s18 (entry + 18) (.add 1 1 5) pc18 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨18, by change 18 < 26; decide⟩)]
    rw [← e19]
    exact copy_add_step s18 1 1 5 (((tempbase) + (2)) + (1)) (1) run19 (by omega) (by omega) (by simp [s18, copyRegisters, baseReg]) (by simp [s18, copyRegisters, baseReg])
  have live19 : s19.liveWords = state.liveWords := rfl
  have pc19 : s19.pc = word width (entry + 19) := rfl
  have run20 : s19.halted = false := rfl
  have e20 : s19.advance.put 0 (word width (guards)) = s20 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s20, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s19 (entry + 19) pc19 (by omega)
    · rfl
  have t20 : programStep resident s19 = some s20 := by
    rw [fetched resident s19 (entry + 19) (.load 0 1) pc19 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨19, by change 19 < 26; decide⟩)]
    rw [← e20]
    exact copy_load_step s19 0 1 ((((tempbase) + (2)) + (1)) + (1)) (word width (guards)) run20 (by omega) (by simp [s19, copyRegisters, baseReg]) (by simpa only [s19] using guardCell)
  have live20 : s20.liveWords = state.liveWords := rfl
  have pc20 : s20.pc = word width (entry + 20) := rfl
  have run21 : s20.halted = false := rfl
  have e21 : s20.advance.put 4 (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) = s21 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s21, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s20 (entry + 20) pc20 (by omega)
    · rfl
  have t21 : programStep resident s20 = some s21 := by
    rw [fetched resident s20 (entry + 20) (.add 4 4 0) pc20 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨20, by change 20 < 26; decide⟩)]
    rw [← e21]
    exact copy_add_step s20 4 4 0 (((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) (guards) run21 (by omega) (by omega) (by simp [s20, copyRegisters, baseReg]) (by simp [s20, copyRegisters, baseReg])
  have live21 : s21.liveWords = state.liveWords := rfl
  have pc21 : s21.pc = word width (entry + 21) := rfl
  have run22 : s21.halted = false := rfl
  have e22 : s21.advance.put 2 (word width ((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards)))) = s22 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s22, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s21 (entry + 21) pc21 (by omega)
    · rfl
  have t22 : programStep resident s21 = some s22 := by
    rw [fetched resident s21 (entry + 21) (.add 2 3 4) pc21 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨21, by change 21 < 26; decide⟩)]
    rw [← e22]
    exact copy_add_step s21 2 3 4 (tempbase) ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards)) run22 (by omega) (by omega) (by simp [s21, copyRegisters, baseReg]) (by simp [s21, copyRegisters, baseReg])
  have live22 : s22.liveWords = state.liveWords := rfl
  have pc22 : s22.pc = word width (entry + 22) := rfl
  have run23 : s22.halted = false := rfl
  have e23 : s22.advance.put 0 (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) = s23 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s23, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s22 (entry + 22) pc22 (by omega)
    · rfl
  have t23 : programStep resident s22 = some s23 := by
    rw [fetched resident s22 (entry + 22) (.copy 0 4) pc22 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨22, by change 22 < 26; decide⟩)]
    rw [← e23]
    exact copy_copy_step s22 0 4 (word width ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) run23 (by simp [s22, copyRegisters])
  have live23 : s23.liveWords = state.liveWords := rfl
  have pc23 : s23.pc = word width (entry + 23) := rfl
  have run24 : s23.halted = false := rfl
  have e24 : s23.advance.put 1 (word width ((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards)))) = s24 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s24, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s23 (entry + 23) pc23 (by omega)
    · rfl
  have t24 : programStep resident s23 = some s24 := by
    rw [fetched resident s23 (entry + 23) (.add 1 3 4) pc23 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨23, by change 23 < 26; decide⟩)]
    rw [← e24]
    exact copy_add_step s23 1 3 4 (tempbase) ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards)) run24 (by omega) (by omega) (by simp [s23, copyRegisters, baseReg]) (by simp [s23, copyRegisters, baseReg])
  have live24 : s24.liveWords = state.liveWords := rfl
  have pc24 : s24.pc = word width (entry + 24) := rfl
  have run25 : s24.halted = false := rfl
  have e25 : s24.advance.put 1 (word width (((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) + (2 ^ width - 1))) = s25 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · simpa only [State.put, s25, Nat.add_assoc, Nat.reduceAdd] using referenceAdvancePC s24 (entry + 24) pc24 (by omega)
    · rfl
  have t25 : programStep resident s24 = some s25 := by
    rw [fetched resident s24 (entry + 24) (.add 1 1 7) pc24 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨24, by change 24 < 26; decide⟩)]
    rw [← e25]
    exact copy_add_step s24 1 1 7 ((tempbase) + ((((((((nodes) + (nodes)) + ((nodes) + (nodes))) + ((nodes) + (nodes))) + (9)) + (roots)) + (children)) + (guards))) (2 ^ width - 1) run25 (by omega) (by omega) (by simp [s24, copyRegisters, baseReg]) (by simp [s24, copyRegisters, baseReg])
  have live25 : s25.liveWords = state.liveWords := rfl
  have pc25 : s25.pc = word width (entry + 25) := rfl
  have run26 : s25.halted = false := rfl
  have e26 : { s25.advance with pc := word width saveEntry } = s26 := by
    apply copy_state_ext
    · intro register
      fin_cases register <;> rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  have t26 : programStep resident s25 = some s26 := by
    rw [fetched resident s25 (entry + 25) (.branchZero 6 (word width saveEntry)) pc25 (by omega)
      (by simpa [originalNormalizationSetupCode] using physical ⟨25, by change 25 < 26; decide⟩)]
    rw [← e26]
    exact copy_branch_zero s25 6 saveEntry run26 (by simp [s25, copyRegisters])
  have live26 : s26.liveWords = state.liveWords := rfl
  have chunk1 : Execution resident state s10 10 state.liveWords := by
    simpa only [live1, live2, live3, live4, live5, live6, live7, live8, live9, live10, live10, live21, max_self, Nat.reduceAdd] using Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.cons t10 (Execution.refl s10))))))))))
  have chunk2 : Execution resident s10 s21 11 state.liveWords := by
    simpa only [live11, live12, live13, live14, live15, live16, live17, live18, live19, live20, live21, live10, live21, max_self, Nat.reduceAdd] using Execution.cons t11 (Execution.cons t12 (Execution.cons t13 (Execution.cons t14 (Execution.cons t15 (Execution.cons t16 (Execution.cons t17 (Execution.cons t18 (Execution.cons t19 (Execution.cons t20 (Execution.cons t21 (Execution.refl s21)))))))))))
  have chunk3 : Execution resident s21 s26 5 state.liveWords := by
    simpa only [live22, live23, live24, live25, live26, live10, live21, max_self, Nat.reduceAdd] using Execution.cons t22 (Execution.cons t23 (Execution.cons t24 (Execution.cons t25 (Execution.cons t26 (Execution.refl s26)))))
  have trace : Execution resident state s26 26 state.liveWords := by
    simpa only [Nat.reduceAdd, Nat.max_self] using chunk1.append (chunk2.append chunk3)
  let packetWords := ((nodes + nodes) + (nodes + nodes) + (nodes + nodes)) + 9 + roots + children + guards
  have packetEq : packetWords = 9 + 6 * nodes + children + guards + roots := by
    dsimp only [packetWords]
    omega
  have countFinal : s26.reg 0 = word width (9 + 6 * nodes + children + guards + roots) := by
    change word width packetWords = _
    rw [packetEq]
  have cursorFinal : s26.reg 1 = word width (tempbase + (9 + 6 * nodes + children + guards + roots) - 1) := by
    change word width ((tempbase + packetWords) + (2 ^ width - 1)) = _
    rw [packetEq]
    exact marker_word_decrement (tempbase + (9 + 6 * nodes + children + guards + roots)) (by omega) capacity
  have endFinal : s26.reg 2 = word width (tempbase + (9 + 6 * nodes + children + guards + roots)) := by
    change word width (tempbase + packetWords) = _
    rw [packetEq]
  have lengthFinal : s26.reg 4 = word width (9 + 6 * nodes + children + guards + roots) := by
    change word width packetWords = _
    rw [packetEq]
  exact ⟨s26, trace, rfl, rfl, rfl, rfl, rfl, countFinal, cursorFinal, endFinal, rfl, lengthFinal, rfl, rfl⟩


/-- The two-instruction rearm actually copies a retained scalar into the loop
counter and branches; it changes no storage and consumes no input. -/
private theorem original_counter_rearm_execution (resident : Program width 8)
    (entry done : Nat) (source : Fin 8) (count : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (held : state.reg source = word width count)
    (zero : state.reg 6 = word width 0) (sourceNotZero : source ≠ 0)
    (first : resident[entry]? = some (.copy 0 source))
    (second : resident[entry + 1]? = some (.branchZero 6 (word width done))) :
    ∃ final, Execution resident state final 2 state.liveWords ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width count ∧ final.liveWords = state.liveWords ∧
      (∀ index : Fin 8, index ≠ 0 → final.reg index = state.reg index) := by
  let middle := state.advance.put 0 (word width count)
  let final := { middle.advance with pc := word width done }
  have middlePosition : middle.pc = word width (entry + 1) := by
    exact RawTransferLoops.advance_position state position (by omega)
  have firstStep : programStep resident state = some middle := by
    rw [RawTransferLoops.fetched resident state entry _ position (by omega) first]
    simp only [step, running, Bool.false_eq_true, ite_false, held, middle]
  have middleZero : middle.reg 6 = word width 0 := by
    simpa only [middle, State.advance, State.put, ite_eq_right (by decide : (6 : Fin 8) ≠ 0)] using zero
  have secondStep : programStep resident middle = some final := by
    rw [RawTransferLoops.fetched resident middle (entry + 1) _ middlePosition (by omega) second]
    exact copy_branch_zero middle 6 done running middleZero
  have middleLive : middle.liveWords = state.liveWords := rfl
  have finalLive : final.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, rfl, running, rfl, rfl, rfl, ?_, finalLive, ?_⟩
  · simpa only [middleLive, finalLive, Nat.max_self] using
      Execution.cons firstStep (Execution.cons secondStep (Execution.refl final))
  · simp only [final, middle, State.advance, State.put, ite_eq_left rfl, ite_true, ite_false]
  · intro index different
    simp only [final, middle, State.advance, State.put, ite_eq_right different]

/-- The release rearm consumes the actual ending heap address saved in register
2 by the executed header-length setup. -/
private theorem original_release_rearm_execution (resident : Program width 8)
    (entry done count : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (held : state.reg 2 = word width count)
    (zero : state.reg 6 = word width 0)
    (physical : RawTransferLoops.CodeAt resident entry (originalReleaseRearmCode width done)) :
    ∃ final, Execution resident state final 2 state.liveWords ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width count ∧ final.liveWords = state.liveWords ∧
      (∀ index : Fin 8, index ≠ 0 → final.reg index = state.reg index) := by
  apply original_counter_rearm_execution resident entry done 2 count state position running room held zero (by decide)
  · simpa [originalReleaseRearmCode, Nat.add_zero] using physical ⟨0, by change 0 < 2; decide⟩
  · simpa [originalReleaseRearmCode] using physical ⟨1, by change 1 < 2; decide⟩

/-- The reload rearm reads the packet length retained in register 4, rather
than a packet-length constant in the resident program. -/
private theorem original_load_rearm_execution (resident : Program width 8)
    (entry done count : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (held : state.reg 4 = word width count)
    (zero : state.reg 6 = word width 0)
    (physical : RawTransferLoops.CodeAt resident entry (originalLoadRearmCode width done)) :
    ∃ final, Execution resident state final 2 state.liveWords ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width count ∧ final.liveWords = state.liveWords ∧
      (∀ index : Fin 8, index ≠ 0 → final.reg index = state.reg index) := by
  apply original_counter_rearm_execution resident entry done 4 count state position running room held zero (by decide)
  · simpa [originalLoadRearmCode, Nat.add_zero] using physical ⟨0, by change 0 < 2; decide⟩
  · simpa [originalLoadRearmCode] using physical ⟨1, by change 1 < 2; decide⟩


private theorem original_save_rearm_execution (resident : Program width 8)
    (entry done base count : Nat) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 4 < 2 ^ width) (positive : 0 < base)
    (capacity : base + count < 2 ^ width)
    (baseReg : state.reg 3 = word width base) (countReg : state.reg 4 = word width count)
    (maskReg : state.reg 7 = word width (2 ^ width - 1)) (zeroReg : state.reg 6 = word width 0)
    (physical : RawTransferLoops.CodeAt resident entry (originalSaveRearmCode width done)) :
    ∃ final, Execution resident state final 4 state.liveWords ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 0 = word width count ∧ final.reg 1 = word width (base + count - 1) ∧
      final.liveWords = state.liveWords ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 1 → final.reg index = state.reg index) := by
  let s1 := state.advance.put 0 (word width count)
  let s2 := s1.advance.put 1 (word width (base + count))
  let s3 := s2.advance.put 1 (word width (base + count - 1))
  let final := { s3.advance with pc := word width done }
  have p1 : s1.pc = word width (entry + 1) := RawTransferLoops.advance_position state position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    change s1.advance.pc = _
    simpa only [Nat.add_assoc] using RawTransferLoops.advance_position s1 p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    change s2.advance.pc = _
    simpa only [Nat.add_assoc] using RawTransferLoops.advance_position s2 p2 (by omega)
  have t0 : programStep resident state = some s1 := by
    have selected : resident[entry]? = some (.copy 0 4) := by
      simpa [originalSaveRearmCode, Nat.add_zero] using physical ⟨0, by change 0 < 4; decide⟩
    rw [RawTransferLoops.fetched resident state entry _ position (by omega) selected]
    simp only [step, running, Bool.false_eq_true, ite_false, countReg, s1]
  have t1 : programStep resident s1 = some s2 := by
    have selected : resident[entry + 1]? = some (.add 1 3 4) := by
      simpa [originalSaveRearmCode] using physical ⟨1, by change 1 < 4; decide⟩
    rw [RawTransferLoops.fetched resident s1 (entry + 1) _ p1 (by omega) selected]
    apply copy_add_step s1 1 3 4 base count running (by omega) (by omega)
    · simpa only [s1, State.advance, State.put, ite_eq_right (by decide : (3 : Fin 8) ≠ 0)] using baseReg
    · simpa only [s1, State.advance, State.put, ite_eq_right (by decide : (4 : Fin 8) ≠ 0)] using countReg
  have decrement : word width ((s2.reg 1).val + (s2.reg 7).val) = word width (base + count - 1) := by
    have firstValue : (word width (base + count)).val = base + count := Nat.mod_eq_of_lt capacity
    have maskValue : (word width (2 ^ width - 1)).val = 2 ^ width - 1 := Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)
    simp only [s2, s1, State.advance, State.put, ite_eq_left rfl, ite_true, ite_false,
      ite_eq_right (by decide : (7 : Fin 8) ≠ 1),
      ite_eq_right (by decide : (7 : Fin 8) ≠ 0), maskReg, firstValue, maskValue]
    exact marker_word_decrement (base + count) (by omega) capacity
  have t2 : programStep resident s2 = some s3 := by
    have selected : resident[entry + 2]? = some (.add 1 1 7) := by
      simpa [originalSaveRearmCode] using physical ⟨2, by change 2 < 4; decide⟩
    rw [RawTransferLoops.fetched resident s2 (entry + 2) _ p2 (by omega) selected]
    simp only [step, show s2.halted = false from running, Bool.false_eq_true, ite_false, decrement, s3]
  have t3 : programStep resident s3 = some final := by
    have selected : resident[entry + 3]? = some (.branchZero 6 (word width done)) := by
      simpa [originalSaveRearmCode] using physical ⟨3, by change 3 < 4; decide⟩
    rw [RawTransferLoops.fetched resident s3 (entry + 3) _ p3 (by omega) selected]
    apply copy_branch_zero s3 6 done running
    simpa only [s3, s2, s1, State.advance, State.put,
      ite_eq_right (by decide : (6 : Fin 8) ≠ 1),
      ite_eq_right (by decide : (6 : Fin 8) ≠ 0)] using zeroReg
  have l1 : s1.liveWords = state.liveWords := rfl
  have l2 : s2.liveWords = state.liveWords := rfl
  have l3 : s3.liveWords = state.liveWords := rfl
  have lf : final.liveWords = state.liveWords := rfl
  refine ⟨final, ?_, rfl, running, rfl, rfl, rfl, ?_, ?_, lf, ?_⟩
  · simpa only [l1, l2, l3, lf, Nat.max_self] using
      Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl final))))
  · simp only [final, s3, s2, s1, State.advance, State.put,
      ite_eq_right (by decide : (0 : Fin 8) ≠ 1), ite_eq_left rfl, ite_true, ite_false]
  · simp only [final, s3, State.advance, State.put, ite_eq_left rfl, ite_true, ite_false]
  · intro index n0 n1
    simp only [final, s3, s2, s1, State.advance, State.put,
      ite_eq_right n1, ite_eq_right n0]


/-- Actual positive-base normalization retains one original packet on the stack
and reloads the other at address zero. All loop counts come from executed
header loads; the temporary heap may contain any number of parser tables. -/
private theorem original_normalization_execution_parts (resident : Program width 8)
    (entry callerEntry tempbase nodes children guards roots : Nat)
    (packet : List (Word width)) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 55 < 2 ^ width) (positive : 0 < tempbase)
    (capacity : tempbase + packet.length < 2 ^ width)
    (packetLength : packet.length = 9 + 6 * nodes + children + guards + roots)
    (heapSize : state.heap.size = tempbase + packet.length)
    (baseReg : state.reg 3 = word width tempbase)
    (nodeCell : state.heap[tempbase]? = some (word width nodes))
    (rootCell : state.heap[tempbase + 2]? = some (word width roots))
    (childCell : state.heap[tempbase + 3]? = some (word width children))
    (guardCell : state.heap[tempbase + 4]? = some (word width guards))
    (packetCells : ∀ index : Nat, ∀ inside : index < packet.length,
      state.heap[tempbase + index]? = some packet[index])
    (setupAt : RawTransferLoops.CodeAt resident entry (originalNormalizationSetupCode width (entry + 26)))
    (firstSaveAt : RawTransferLoops.CodeAt resident (entry + 26)
      (RawTransferLoops.reverseSaveCode width (entry + 26) (entry + 32)))
    (saveRearmAt : RawTransferLoops.CodeAt resident (entry + 32) (originalSaveRearmCode width (entry + 36)))
    (secondSaveAt : RawTransferLoops.CodeAt resident (entry + 36)
      (RawTransferLoops.reverseSaveCode width (entry + 36) (entry + 42)))
    (releaseRearmAt : RawTransferLoops.CodeAt resident (entry + 42) (originalReleaseRearmCode width (entry + 44)))
    (releaseAt : RawTransferLoops.CodeAt resident (entry + 44)
      (RawTransferLoops.countedReleaseCode width (entry + 44) (entry + 48)))
    (loadRearmAt : RawTransferLoops.CodeAt resident (entry + 48) (originalLoadRearmCode width (entry + 50)))
    (loadAt : RawTransferLoops.CodeAt resident (entry + 50) (countedOriginalLoadCode width (entry + 50) callerEntry)) :
    ∃ final peak, Execution resident state final
      (17 * packet.length + 4 * (tempbase + packet.length) + 38) peak ∧
      peak ≤ state.liveWords + 2 * packet.length ∧ final.heap = packet.toArray ∧
      final.stack = packet ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width callerEntry ∧ final.halted = false := by
  have countFits : packet.length < 2 ^ width := by omega
  obtain ⟨prepared, preparation, preparedHeap, preparedStack, preparedOutput,
    preparedPC, preparedRunning, preparedCount, preparedCursor, preparedEnd,
    preparedBase, preparedLength, preparedZero, preparedMask⟩ :=
    original_normalization_setup_execution resident entry (entry + 26) tempbase nodes children guards roots state
      position running (by omega) positive (by simpa only [packetLength] using capacity)
      baseReg nodeCell rootCell childCell guardCell setupAt
  have preparedLive : prepared.liveWords = state.liveWords := by
    simp only [State.liveWords, preparedHeap, preparedStack, preparedOutput]
  have preparedCount' : prepared.reg 0 = word width packet.length := by simpa only [packetLength] using preparedCount
  have preparedCursor' : prepared.reg 1 = word width (tempbase + packet.length - 1) := by simpa only [packetLength] using preparedCursor
  have preparedEnd' : prepared.reg 2 = word width (tempbase + packet.length) := by simpa only [packetLength] using preparedEnd
  have preparedLength' : prepared.reg 4 = word width packet.length := by simpa only [packetLength] using preparedLength
  have preparedBase' : prepared.reg 3 = word width tempbase := preparedBase.trans baseReg
  obtain ⟨saved, savePeak, firstSave, firstSpace, savedHeap, savedStack, savedOutput,
    savedPC, savedRunning, savedCount, savedFrame⟩ :=
    RawTransferLoops.reverse_save_execution resident (entry + 26) (entry + 32) tempbase packet prepared
      preparedPC preparedRunning (by omega) positive capacity countFits preparedCount' preparedCursor'
      preparedMask preparedZero (by intro index inside; rw [preparedHeap]; exact packetCells index inside) firstSaveAt
  have savedBase : saved.reg 3 = word width tempbase := (savedFrame 3 (by decide) (by decide) (by decide)).trans preparedBase'
  have savedLength : saved.reg 4 = word width packet.length := (savedFrame 4 (by decide) (by decide) (by decide)).trans preparedLength'
  have savedEnd : saved.reg 2 = word width (tempbase + packet.length) := (savedFrame 2 (by decide) (by decide) (by decide)).trans preparedEnd'
  have savedZero : saved.reg 6 = word width 0 := (savedFrame 6 (by decide) (by decide) (by decide)).trans preparedZero
  have savedMask : saved.reg 7 = word width (2 ^ width - 1) := (savedFrame 7 (by decide) (by decide) (by decide)).trans preparedMask
  have savedLive : saved.liveWords = state.liveWords + packet.length := by
    simp only [State.liveWords, savedHeap, savedStack, savedOutput,
      preparedHeap, preparedStack, preparedOutput, List.length_append]
    omega
  obtain ⟨rearmed, rearm, rearmedPC, rearmedRunning, rearmedHeap, rearmedStack, rearmedOutput,
    rearmedCount, rearmedCursor, rearmedLive, rearmedFrame⟩ :=
    original_save_rearm_execution resident (entry + 32) (entry + 36) tempbase packet.length saved
      savedPC savedRunning (by omega) positive capacity savedBase savedLength savedMask savedZero saveRearmAt
  have rearmedEnd : rearmed.reg 2 = word width (tempbase + packet.length) := (rearmedFrame 2 (by decide) (by decide)).trans savedEnd
  have rearmedLength : rearmed.reg 4 = word width packet.length := (rearmedFrame 4 (by decide) (by decide)).trans savedLength
  have rearmedZero : rearmed.reg 6 = word width 0 := (rearmedFrame 6 (by decide) (by decide)).trans savedZero
  have rearmedMask : rearmed.reg 7 = word width (2 ^ width - 1) := (rearmedFrame 7 (by decide) (by decide)).trans savedMask
  obtain ⟨twiceSaved, secondPeak, secondSave, secondSpace, twiceHeap, twiceStack, twiceOutput,
    twicePC, twiceRunning, twiceCount, twiceFrame⟩ :=
    RawTransferLoops.reverse_save_execution resident (entry + 36) (entry + 42) tempbase packet rearmed
      rearmedPC rearmedRunning (by omega) positive capacity countFits rearmedCount rearmedCursor
      rearmedMask rearmedZero (by intro index inside; rw [rearmedHeap, savedHeap, preparedHeap]; exact packetCells index inside) secondSaveAt
  have twiceEnd : twiceSaved.reg 2 = word width (tempbase + packet.length) := (twiceFrame 2 (by decide) (by decide) (by decide)).trans rearmedEnd
  have twiceLength : twiceSaved.reg 4 = word width packet.length := (twiceFrame 4 (by decide) (by decide) (by decide)).trans rearmedLength
  have twiceZero : twiceSaved.reg 6 = word width 0 := (twiceFrame 6 (by decide) (by decide) (by decide)).trans rearmedZero
  have twiceMask : twiceSaved.reg 7 = word width (2 ^ width - 1) := (twiceFrame 7 (by decide) (by decide) (by decide)).trans rearmedMask
  have twiceLive : twiceSaved.liveWords = state.liveWords + 2 * packet.length := by
    simp only [State.liveWords, twiceHeap, twiceStack, twiceOutput, rearmedHeap, rearmedStack,
      rearmedOutput, savedHeap, savedStack, savedOutput, preparedHeap, preparedStack, preparedOutput, List.length_append]
    omega
  obtain ⟨releaseReady, releaseRearm, releaseReadyPC, releaseReadyRunning, releaseReadyHeap,
    releaseReadyStack, releaseReadyOutput, releaseReadyCount, releaseReadyLive, releaseReadyFrame⟩ :=
    original_release_rearm_execution resident (entry + 42) (entry + 44) (tempbase + packet.length) twiceSaved
      twicePC twiceRunning (by omega) twiceEnd twiceZero releaseRearmAt
  have releaseCount : releaseReady.heap.size = tempbase + packet.length := by
    rw [releaseReadyHeap, twiceHeap, rearmedHeap, savedHeap, preparedHeap]; exact heapSize
  obtain ⟨released, releasePeak, release, releaseSpace, releasedHeap, releasedStack, releasedOutput,
    releasedPC, releasedRunning, releasedCount, releasedFrame⟩ :=
    RawTransferLoops.counted_release_execution resident (entry + 44) (entry + 48) (tempbase + packet.length)
      releaseReady releaseReadyPC releaseReadyRunning (by omega) releaseCount capacity releaseReadyCount
      ((releaseReadyFrame 7 (by decide)).trans twiceMask) ((releaseReadyFrame 6 (by decide)).trans twiceZero) releaseAt
  have releasedLength : released.reg 4 = word width packet.length :=
    (releasedFrame 4 (by decide)).trans ((releaseReadyFrame 4 (by decide)).trans twiceLength)
  have releasedZero : released.reg 6 = word width 0 :=
    (releasedFrame 6 (by decide)).trans ((releaseReadyFrame 6 (by decide)).trans twiceZero)
  obtain ⟨loadReady, loadRearm, loadReadyPC, loadReadyRunning, loadReadyHeap, loadReadyStack,
    loadReadyOutput, loadReadyCount, loadReadyLive, loadReadyFrame⟩ :=
    original_load_rearm_execution resident (entry + 48) (entry + 50) packet.length released
      releasedPC releasedRunning (by omega) releasedLength releasedZero loadRearmAt
  have retainedInput : loadReady.stack = packet ++ (packet ++ state.stack) := by
    rw [loadReadyStack, releasedStack, releaseReadyStack, twiceStack, rearmedStack, savedStack, preparedStack]
  obtain ⟨final, loadPeak, load, loadSpace, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
    finalCount, finalFrame⟩ :=
    counted_original_load_execution resident (entry + 50) callerEntry packet (packet ++ state.stack) loadReady
      loadReadyPC loadReadyRunning (by omega) countFits loadReadyCount
      ((loadReadyFrame 7 (by decide)).trans ((releasedFrame 7 (by decide)).trans ((releaseReadyFrame 7 (by decide)).trans twiceMask)))
      ((loadReadyFrame 6 (by decide)).trans releasedZero) retainedInput
      (by rw [loadReadyHeap, releasedHeap]; simp only [Array.size_empty] <;> omega) loadAt
  have releasedLive : released.liveWords ≤ state.liveWords + 2 * packet.length :=
    (Execution.final_storage_le release).trans (releaseSpace.trans (by rw [releaseReadyLive, twiceLive]))
  have allTrace := preparation.append (firstSave.append (rearm.append (secondSave.append
    (releaseRearm.append (release.append (loadRearm.append load))))))
  refine ⟨final, max state.liveWords (max savePeak (max saved.liveWords
    (max secondPeak (max twiceSaved.liveWords (max releasePeak (max released.liveWords loadPeak)))))),
    ?_, ?_, ?_, finalStack, ?_, finalPC, finalRunning⟩
  · convert allTrace using 1 <;> omega
  · apply max_le_iff.mpr
    constructor
    · omega
    · apply max_le_iff.mpr
      constructor
      · rw [preparedLive] at firstSpace; omega
      · apply max_le_iff.mpr
        constructor
        · rw [savedLive]; omega
        · apply max_le_iff.mpr
          constructor
          · rw [rearmedLive, savedLive] at secondSpace; omega
          · apply max_le_iff.mpr
            constructor
            · rw [twiceLive]
            · apply max_le_iff.mpr
              constructor
              · rw [releaseReadyLive, twiceLive] at releaseSpace; exact releaseSpace
              · apply max_le_iff.mpr
                constructor
                · exact releasedLive
                · rw [loadReadyLive] at loadSpace; exact loadSpace.trans releasedLive
  · rw [finalHeap, loadReadyHeap, releasedHeap]; simp only [Array.empty_append]
  · exact finalOutput.trans (loadReadyOutput.trans (releasedOutput.trans (releaseReadyOutput.trans
      (twiceOutput.trans (rearmedOutput.trans (savedOutput.trans preparedOutput))))))


/-- Actual positive-base normalization retains one original packet on the stack
and reloads the other at address zero. All loop counts come from executed
header loads; the temporary heap may contain any number of parser tables. -/
theorem original_normalization_execution (resident : Program width 8)
    (entry callerEntry tempbase nodes children guards roots : Nat)
    (packet : List (Word width)) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 55 < 2 ^ width) (positive : 0 < tempbase)
    (capacity : tempbase + packet.length < 2 ^ width)
    (packetLength : packet.length = 9 + 6 * nodes + children + guards + roots)
    (heapSize : state.heap.size = tempbase + packet.length)
    (baseReg : state.reg 3 = word width tempbase)
    (nodeCell : state.heap[tempbase]? = some (word width nodes))
    (rootCell : state.heap[tempbase + 2]? = some (word width roots))
    (childCell : state.heap[tempbase + 3]? = some (word width children))
    (guardCell : state.heap[tempbase + 4]? = some (word width guards))
    (packetCells : ∀ index : Nat, ∀ inside : index < packet.length,
      state.heap[tempbase + index]? = some packet[index])
    (physical : RawTransferLoops.CodeAt resident entry (originalNormalizationCode width entry callerEntry)) :
    ∃ final peak, Execution resident state final
      (17 * packet.length + 4 * (tempbase + packet.length) + 38) peak ∧
      peak ≤ state.liveWords + 2 * packet.length ∧ final.heap = packet.toArray ∧
      final.stack = packet ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width callerEntry ∧ final.halted = false := by
  let setup : Program width 8 := originalNormalizationSetupCode width (entry + 26)
  let saveFirst : Program width 8 := RawTransferLoops.reverseSaveCode width (entry + 26) (entry + 32)
  let rearmSave : Program width 8 := originalSaveRearmCode width (entry + 36)
  let saveSecond : Program width 8 := RawTransferLoops.reverseSaveCode width (entry + 36) (entry + 42)
  let rearmRelease : Program width 8 := originalReleaseRearmCode width (entry + 44)
  let release : Program width 8 := RawTransferLoops.countedReleaseCode width (entry + 44) (entry + 48)
  let rearmLoad : Program width 8 := originalLoadRearmCode width (entry + 50)
  let load : Program width 8 := countedOriginalLoadCode width (entry + 50) callerEntry
  let whole := originalNormalizationCode width entry callerEntry
  have setupAt : RawTransferLoops.CodeAt resident (entry + 0) setup := by
    have selected := extract_copy_section resident whole (#[]) setup (saveFirst ++ rearmSave ++ saveSecond ++ rearmRelease ++ release ++ rearmLoad ++ load) entry 0 26
      (by simp only [whole, originalNormalizationCode, setup, saveFirst, rearmSave, saveSecond, rearmRelease, release, rearmLoad, load, Array.append_assoc, Array.empty_append, Array.append_empty])
      (by rfl)
      (by simp only [setup, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append]) physical
    intro phase
    have inside : phase.val < 26 := by simpa only [setup, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append] using phase.isLt
    exact selected ⟨phase.val, inside⟩
  have saveFirstAt : RawTransferLoops.CodeAt resident (entry + 26) saveFirst := by
    have selected := extract_copy_section resident whole (setup) saveFirst (rearmSave ++ saveSecond ++ rearmRelease ++ release ++ rearmLoad ++ load) entry 26 6
      (by simp only [whole, originalNormalizationCode, setup, saveFirst, rearmSave, saveSecond, rearmRelease, release, rearmLoad, load, Array.append_assoc, Array.empty_append, Array.append_empty])
      (by simp only [setup, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append, Array.size_empty] <;> omega)
      (by simp only [saveFirst, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append]) physical
    intro phase
    have inside : phase.val < 6 := by simpa only [saveFirst, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append] using phase.isLt
    exact selected ⟨phase.val, inside⟩
  have rearmSaveAt : RawTransferLoops.CodeAt resident (entry + 32) rearmSave := by
    have selected := extract_copy_section resident whole (setup ++ saveFirst) rearmSave (saveSecond ++ rearmRelease ++ release ++ rearmLoad ++ load) entry 32 4
      (by simp only [whole, originalNormalizationCode, setup, saveFirst, rearmSave, saveSecond, rearmRelease, release, rearmLoad, load, Array.append_assoc, Array.empty_append, Array.append_empty])
      (by simp only [setup, saveFirst, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append, Array.size_empty] <;> omega)
      (by simp only [rearmSave, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append]) physical
    intro phase
    have inside : phase.val < 4 := by simpa only [rearmSave, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append] using phase.isLt
    exact selected ⟨phase.val, inside⟩
  have saveSecondAt : RawTransferLoops.CodeAt resident (entry + 36) saveSecond := by
    have selected := extract_copy_section resident whole (setup ++ saveFirst ++ rearmSave) saveSecond (rearmRelease ++ release ++ rearmLoad ++ load) entry 36 6
      (by simp only [whole, originalNormalizationCode, setup, saveFirst, rearmSave, saveSecond, rearmRelease, release, rearmLoad, load, Array.append_assoc, Array.empty_append, Array.append_empty])
      (by simp only [setup, saveFirst, rearmSave, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append, Array.size_empty] <;> omega)
      (by simp only [saveSecond, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append]) physical
    intro phase
    have inside : phase.val < 6 := by simpa only [saveSecond, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append] using phase.isLt
    exact selected ⟨phase.val, inside⟩
  have rearmReleaseAt : RawTransferLoops.CodeAt resident (entry + 42) rearmRelease := by
    have selected := extract_copy_section resident whole (setup ++ saveFirst ++ rearmSave ++ saveSecond) rearmRelease (release ++ rearmLoad ++ load) entry 42 2
      (by simp only [whole, originalNormalizationCode, setup, saveFirst, rearmSave, saveSecond, rearmRelease, release, rearmLoad, load, Array.append_assoc, Array.empty_append, Array.append_empty])
      (by simp only [setup, saveFirst, rearmSave, saveSecond, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append, Array.size_empty] <;> omega)
      (by simp only [rearmRelease, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append]) physical
    intro phase
    have inside : phase.val < 2 := by simpa only [rearmRelease, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append] using phase.isLt
    exact selected ⟨phase.val, inside⟩
  have releaseAt : RawTransferLoops.CodeAt resident (entry + 44) release := by
    have selected := extract_copy_section resident whole (setup ++ saveFirst ++ rearmSave ++ saveSecond ++ rearmRelease) release (rearmLoad ++ load) entry 44 4
      (by simp only [whole, originalNormalizationCode, setup, saveFirst, rearmSave, saveSecond, rearmRelease, release, rearmLoad, load, Array.append_assoc, Array.empty_append, Array.append_empty])
      (by simp only [setup, saveFirst, rearmSave, saveSecond, rearmRelease, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append, Array.size_empty] <;> omega)
      (by simp only [release, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append]) physical
    intro phase
    have inside : phase.val < 4 := by simpa only [release, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append] using phase.isLt
    exact selected ⟨phase.val, inside⟩
  have rearmLoadAt : RawTransferLoops.CodeAt resident (entry + 48) rearmLoad := by
    have selected := extract_copy_section resident whole (setup ++ saveFirst ++ rearmSave ++ saveSecond ++ rearmRelease ++ release) rearmLoad (load) entry 48 2
      (by simp only [whole, originalNormalizationCode, setup, saveFirst, rearmSave, saveSecond, rearmRelease, release, rearmLoad, load, Array.append_assoc, Array.empty_append, Array.append_empty])
      (by simp only [setup, saveFirst, rearmSave, saveSecond, rearmRelease, release, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append, Array.size_empty] <;> omega)
      (by simp only [rearmLoad, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append]) physical
    intro phase
    have inside : phase.val < 2 := by simpa only [rearmLoad, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append] using phase.isLt
    exact selected ⟨phase.val, inside⟩
  have loadAt : RawTransferLoops.CodeAt resident (entry + 50) load := by
    have selected := extract_copy_section resident whole (setup ++ saveFirst ++ rearmSave ++ saveSecond ++ rearmRelease ++ release ++ rearmLoad) load (#[]) entry 50 5
      (by simp only [whole, originalNormalizationCode, setup, saveFirst, rearmSave, saveSecond, rearmRelease, release, rearmLoad, load, Array.append_assoc, Array.empty_append, Array.append_empty])
      (by simp only [setup, saveFirst, rearmSave, saveSecond, rearmRelease, release, rearmLoad, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append, Array.size_empty] <;> omega)
      (by simp only [load, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append]) physical
    intro phase
    have inside : phase.val < 5 := by simpa only [load, original_normalization_setup_code_size, original_save_rearm_code_size, original_release_rearm_code_size, original_load_rearm_code_size, counted_original_load_code_size, RawTransferLoops.reverseSaveCode_size, RawTransferLoops.countedReleaseCode_size, Array.size_append] using phase.isLt
    exact selected ⟨phase.val, inside⟩
  exact original_normalization_execution_parts resident entry callerEntry tempbase nodes children guards roots packet state
    position running room positive capacity packetLength heapSize baseReg nodeCell rootCell childCell guardCell packetCells
    (by simpa only [Nat.add_zero, setup] using setupAt) saveFirstAt rearmSaveAt saveSecondAt rearmReleaseAt releaseAt rearmLoadAt loadAt


end Controller.Cost.RawTypedCopy
