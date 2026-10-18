module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.RawSharedHandoff

@[expose] public section

/-! The resident ordered-copy caller transfers the numbered packet into the
shared evaluator. Its instructions depend on original counts, while numbering
and assignment values are read from the retained source and runtime tables. -/
namespace Controller.Cost.RawSharedOrdered
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.RawTypedCopy Controller.Cost.RegisterWiden
open Controller.Cost.RawAdapterProgram Controller.Cost.RawTransferLoops

private theorem typedSaveSetupCode_size (width count entry : ℕ) :
    (typedSaveSetupCode width count entry).size = 8 := rfl

theorem takePrefix (resident : Program width 8) (entry : ℕ)
    (first rest : Program width 8) (stored : CodeAt resident entry (first ++ rest)) :
    CodeAt resident entry first := by
  intro phase
  have h := stored ⟨phase.val, by simp only [Array.size_append]; omega⟩
  simpa only [Array.getElem?_append_left phase.isLt] using h

theorem takeSuffix (resident : Program width 8) (entry : ℕ)
    (first rest : Program width 8) (stored : CodeAt resident entry (first ++ rest)) :
    CodeAt resident (entry + first.size) rest := by
  intro phase
  have h := stored ⟨first.size + phase.val, by simp only [Array.size_append]; omega⟩
  change resident[entry + (first.size + phase.val)]? = (first ++ rest)[first.size + phase.val]? at h
  rw [Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at h
  simpa only [Nat.add_assoc] using h

def kernel (width channels nodes children guards roots : ℕ) : Program width 8 :=
  widenProgram (UniformDAGRuntimeOutputs.shapeProgram width channels nodes children guards roots)

@[simp] theorem kernel_size (width channels nodes children guards roots : ℕ) :
    (kernel width channels nodes children guards roots).size = 174 + 2 * channels := by
  simp [kernel, widenProgram]

def packetLength (nodes children guards roots : ℕ) : ℕ :=
  5 + 6 * nodes + children + guards + roots

/-- The source copy, transfer loops, handoff, and relocated shared kernel form
one resident instruction array. -/
@[irreducible] def code (width channels nodes children guards roots base entry : ℕ) : Program width 8 :=
  orderedTypedCopyCode width nodes children base entry (entry + 207) ++
  (typedOriginRecoverCode width nodes base ++
  (typedSaveSetupCode width (packetLength nodes children guards roots) (entry + 217) ++
  (reverseSaveCode width (entry + 217) (entry + 223) ++
  (typedReleaseSetupCode width (entry + 225) ++
  (countedReleaseCode width (entry + 225) (entry + 229) ++
  (typedColdHandoffCode width (entry + 231) ++
    (kernel width channels nodes children guards roots).map (relocatedInstruction (entry + 231))))))))

@[simp] theorem code_size (width channels nodes children guards roots base entry : ℕ) :
    (code width channels nodes children guards roots base entry).size = 405 + 2 * channels := by
  simp [code, orderedTypedCopyCode_size, typedOriginRecoverCode_size,
    typedSaveSetupCode, typedReleaseSetupCode_size, typedColdHandoffCode_size]; omega

set_option maxHeartbeats 2000000 in
/-- The produced ordering is copied, saved, and evaluated in one machine run.
Each stored root reads the shared table; no per-root cone work is charged. -/
theorem execution (resident : Program width 8) (initial : State width 8)
    (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) (assignment : Assignment channels)
    (suffixWords : List (Word width)) (H base rankBase entry : ℕ)
    (image : OriginalImageStored initial.heap H channels raw)
    (rawCell : initial.heap[Controller.Horn.WorklistFIFO.activeSlot (n := raw.nodes.size) base]? =
      some (word width H))
    (queue : ∀ index : Fin numbering.order.length,
      initial.heap[Controller.Horn.WorklistMark.queueStart (n := raw.nodes.size) base + index.val]? =
        some (word width (numbering.order[index.val].val)))
    (ranks : ∀ index : Fin numbering.order.length,
      initial.heap[rankBase + numbering.order[index.val].val]? = some (word width index.val))
    (physical : CodeAt resident entry (code width channels raw.nodes.size
      (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
      raw.roots.length base entry))
    (position : initial.pc = word width entry) (running : initial.halted = false)
    (codeFits : entry + (code width channels raw.nodes.size
      (rowChildren (originalRows raw)).length (rowGuards (originalRows raw)).length
      raw.roots.length base entry).size < 2 ^ width)
    (capacity : channels + initial.heap.size +
      (numberedPacketWords (width := width) raw valid numbering).length < 2 ^ width)
    (evalCapacity : 256 * (numbering.toDAG.countedSize + 1) < 2 ^ width)
    (allocation : initial.heap.size = rankBase + raw.nodes.size)
    (rankHeld : initial.reg 4 = word width rankBase)
    (scratchBefore : base + 4 * raw.nodes.size + 4 ≤ H) (rankAfter : H ≤ rankBase)
    (inputStack : initial.stack = List.ofFn (fun channel => boolWord width (assignment channel)) ++ suffixWords) :
    ∃ final ticks peak, Execution resident initial final ticks peak ∧
      ticks ≤ 276 * numbering.toDAG.countedSize + 4 * initial.heap.size + 171 ∧
      peak ≤ max (initial.liveWords +
        2 * (numberedPacketWords (width := width) raw valid numbering).length)
        (8 * numbering.toDAG.countedSize + 18 + suffixWords.length + initial.output.length) ∧
      final.stack = suffixWords ∧
      final.output = ((numbering.toDAG.outputValues assignment).map (boolWord width)).reverse ++ initial.output ∧
      final.halted = true := by
  let graph := numbering.toDAG
  let rows := numberedRows raw valid numbering
  let roots := graph.roots.map Fin.val
  let E := (rowChildren (originalRows raw)).length
  let U := (rowGuards (originalRows raw)).length
  let P := (numberedPacketWords (width := width) raw valid numbering).length
  have matched : RowsMatch graph rows := numbered_rows_match raw valid numbering
  have heads : HeadsMatch graph rows matched := numbered_rows_heads raw valid numbering
  have rootMatches : RootsMatch graph roots := rfl
  have nodesEq : graph.nodeCount = raw.nodes.size := numbering.toDAG_nodeCount
  have rootsEq : graph.roots.length = raw.roots.length := RawNumberingCounts.numbered_roots raw valid numbering
  have sourceCounts : (rowChildren rows).length = E ∧ (rowGuards rows).length = U :=
    numbered_incidence_image raw valid numbering
  have graphCounts := matched_incidence_lengths graph rows matched
  have childEq : graph.childIncidences = E := graphCounts.1.symm.trans sourceCounts.1
  have guardEq : graph.guardIncidences = U := graphCounts.2.symm.trans sourceCounts.2
  have counted : graph.countedSize = channels + raw.nodes.size + E + U + raw.roots.length := by
    simpa only [nodesEq, childEq, guardEq, rootsEq] using graph.countedSize_eq
  have packetEq : numberedPacketWords (width := width) raw valid numbering =
      (inputPacket channels 0 rows roots).map (word width) := numbered_cold_input_words raw valid numbering
  have lengthEq : P = packetLength raw.nodes.size E U raw.roots.length := by
    change (numberedPacketWords (width := width) raw valid numbering).length = _
    rw [packetEq, List.length_map, matched_input_packet_length 0 graph rows roots matched rootMatches]
    simp only [packetLength, nodesEq, childEq, guardEq, rootsEq]
  have packetNatLength : (inputPacket channels 0 rows roots).length = P := by
    have h := congrArg List.length packetEq
    simpa only [P, List.length_map] using h.symm
  change CodeAt resident entry (code width channels raw.nodes.size E U raw.roots.length base entry) at physical
  unfold code at physical
  have copyPart := takePrefix resident entry
    (orderedTypedCopyCode width raw.nodes.size E base entry (entry + 207)) _ physical
  have r1 := takeSuffix resident entry
    (orderedTypedCopyCode width raw.nodes.size E base entry (entry + 207)) _ physical
  simp only [orderedTypedCopyCode_size] at r1
  have recoverPart := takePrefix resident (entry + 207) (typedOriginRecoverCode width raw.nodes.size base) _ r1
  have r2 := takeSuffix resident (entry + 207) (typedOriginRecoverCode width raw.nodes.size base) _ r1
  simp only [typedOriginRecoverCode_size, Nat.add_assoc, Nat.reduceAdd] at r2
  have setupPart := takePrefix resident (entry + 209)
    (typedSaveSetupCode width (packetLength raw.nodes.size E U raw.roots.length) (entry + 217)) _ r2
  have r3 := takeSuffix resident (entry + 209)
    (typedSaveSetupCode width (packetLength raw.nodes.size E U raw.roots.length) (entry + 217)) _ r2
  simp only [typedSaveSetupCode_size, Nat.add_assoc, Nat.reduceAdd] at r3
  have savePart := takePrefix resident (entry + 217) (reverseSaveCode width (entry + 217) (entry + 223)) _ r3
  have r4 := takeSuffix resident (entry + 217) (reverseSaveCode width (entry + 217) (entry + 223)) _ r3
  simp only [reverseSaveCode_size, Nat.add_assoc, Nat.reduceAdd] at r4
  have releaseSetupPart := takePrefix resident (entry + 223) (typedReleaseSetupCode width (entry + 225)) _ r4
  have r5 := takeSuffix resident (entry + 223) (typedReleaseSetupCode width (entry + 225)) _ r4
  simp only [typedReleaseSetupCode_size, Nat.add_assoc, Nat.reduceAdd] at r5
  have releasePart := takePrefix resident (entry + 225) (countedReleaseCode width (entry + 225) (entry + 229)) _ r5
  have r6 := takeSuffix resident (entry + 225) (countedReleaseCode width (entry + 225) (entry + 229)) _ r5
  simp only [countedReleaseCode_size, Nat.add_assoc, Nat.reduceAdd] at r6
  have handoffPart := takePrefix resident (entry + 229) (typedColdHandoffCode width (entry + 231)) _ r6
  have kernelPart := takeSuffix resident (entry + 229) (typedColdHandoffCode width (entry + 231)) _ r6
  simp only [typedColdHandoffCode_size, Nat.add_assoc, Nat.reduceAdd] at kernelPart
  have kernelEq : widenProgram (UniformDAGRuntimeOutputs.program width channels rows roots assignment) =
      kernel width channels raw.nodes.size E U raw.roots.length := by
    simp only [kernel, UniformDAGRuntimeOutputs.program_shape, matched.length_eq, nodesEq,
      sourceCounts.1, sourceCounts.2, roots, List.length_map, rootsEq]
  have coldPhysical : ∀ index (inside : index <
      (widenProgram (UniformDAGRuntimeOutputs.program width channels rows roots assignment)).size),
      resident[(entry + 231) + index]? = some (relocatedInstruction (entry + 231)
        ((widenProgram (UniformDAGRuntimeOutputs.program width channels rows roots assignment))[index]'inside)) := by
    intro index inside
    simp only [kernelEq] at inside ⊢
    have h := kernelPart ⟨index, by simpa using inside⟩
    simpa only [Array.getElem?_map, Array.getElem?_eq_getElem inside, Option.map_some] using h
  have codeBound : entry + (405 + 2 * channels) < 2 ^ width := by simpa only [code_size] using codeFits
  obtain ⟨copied, copyTicks, copyPeak, copyTrace, copyTime, copySpace, copyPC, copyRunning,
      copiedCells, copiedSize, retainedImage, retainedQueue, retainedRanks, copiedStack,
      copiedOutput, copiedRank, copiedZero, copiedMask, originCell⟩ :=
    ordered_copy_execution resident raw valid numbering initial H base rankBase entry (entry + 207)
      image rawCell queue ranks
      (by
        intro phase
        exact copyPart ⟨phase.val, by rw [orderedTypedCopyCode_size]; exact phase.isLt⟩)
      position running (by omega) capacity allocation rankHeld
      scratchBefore rankAfter
  have copiedLive : copied.liveWords = initial.liveWords + P := by
    simp only [State.liveWords, copiedSize, copiedStack, copiedOutput, P]
    omega
  obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, finalStack, finalOutput, finalHalted⟩ :=
    RawSharedHandoff.transfer_execution resident copied graph rows roots matched heads rootMatches
      assignment suffixWords raw.nodes.size base initial.heap.size (entry + 207) (entry + 209)
      (entry + 217) (entry + 223) (entry + 225) (entry + 229) (entry + 231) evalCapacity
      coldPhysical (by rw [kernelEq, kernel_size]; omega) recoverPart
      (by simpa only [CodeAt, typedSaveSetupCode_size, List.length_map, packetNatLength, lengthEq] using setupPart)
      savePart releaseSetupPart releasePart handoffPart (by omega) copyPC copyRunning
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by rw [packetNatLength, lengthEq]; unfold packetLength; omega)
      (by rw [packetNatLength]; omega)
      (by rw [packetNatLength]; exact copiedSize)
      (by unfold Controller.Horn.WorklistBucketReady.nextSlot; omega) originCell
      (by simpa only [← packetEq] using copiedCells) (copiedStack.trans inputStack)
  have joined := copyTrace.append restTrace
  refine ⟨final, _, _, joined, ?_, ?_, finalStack, ?_, finalHalted⟩
  · change copyTicks + restTicks ≤ 276 * graph.countedSize + 4 * initial.heap.size + 171
    rw [packetNatLength, copiedSize] at restTime
    change restTicks ≤ 6 * P + 4 * (initial.heap.size + P) + 97 * graph.countedSize + 53 at restTime
    rw [lengthEq] at restTime
    dsimp only [packetLength] at restTime
    omega
  · rw [packetNatLength, copiedLive, copiedOutput] at restSpace
    change restPeak ≤ max (initial.liveWords + P + P)
      (8 * graph.countedSize + 18 + suffixWords.length + initial.output.length) at restSpace
    apply max_le
    · exact le_trans copySpace (le_trans (by omega) (le_max_left _ _))
    · simpa only [P, graph, Nat.two_mul, Nat.add_assoc] using restSpace
  · simpa only [copiedOutput] using finalOutput

/-- The numbered graph has exactly the original source's charged counts. -/
theorem numbered_counted_size (raw : RawDAG) (valid : raw.WellFormed channels)
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

/-- The raw input's chosen word width supplies the shared evaluator's capacity;
it is not an additional machine-fit assumption. -/
theorem raw_evaluation_capacity (raw : RawDAG) (valid : raw.WellFormed channels)
    (numbering : (raw.toUnordered valid).Numbering) :
    256 * (numbering.toDAG.countedSize + 1) < 2 ^ rawExecutionWidth channels raw := by
  rw [numbered_counted_size]
  let size := channels + raw.nodes.size + (rowChildren (originalRows raw)).length +
    (rowGuards (originalRows raw)).length + raw.roots.length
  change 256 * (size + 1) < 2 ^ (Nat.log 2 (size + 1) + 13)
  have basic := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (size + 1)
  have scaled := Nat.mul_lt_mul_of_pos_left basic (by decide : 0 < 256)
  have room : 256 * 2 ^ (Nat.log 2 (size + 1) + 1) ≤ 2 ^ (Nat.log 2 (size + 1) + 13) := by
    simp only [Nat.pow_add, Nat.pow_one, Nat.reducePow]
    omega
  exact lt_of_lt_of_le scaled room

end Controller.Cost.RawSharedOrdered
