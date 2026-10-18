module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverWorking

@[expose] public section

/-! The fetched seek prefix reads the previous result's baseline bit and
branches to either the sibling query or the skip continuation. -/
namespace Controller.Cost.EnumerationDriverSeekStep
open Controller.Decoder Controller.Decoder.Enumeration Controller.Native
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops
open Controller.Cost.SharedDetectorAssembly
open Controller.Cost.EnumerationDriverPrefix Controller.Cost.EnumerationDriverQuery

/-- Zero-cursor test, decrement and read of the preceding baseline bit. -/
def headCode (width packetSize halt seekTry : Nat) : List (Instruction width 8) :=
  (SharedTagCompare.code width halt 0 3).toList ++
    EnumerationCounter.code width (2 ^ width - 1) ++
    EnumerationDriverCode.readBit width packetSize ++
    [.branchZero 1 (word width seekTry)]

/-- The true-bit continuation, with a separate forced-target branch. -/
def tailCode (parameters : Parameters) (width packetSize seek seekForced : Nat) :
    List (Instruction width 8) :=
  (if parameters.buses = 1 then
      (SharedTagCompare.code width seekForced parameters.bridge.target.val 3).toList else []) ++
    EnumerationMaskWrite.code width packetSize false ++
    EnumerationMaskWrite.code width (packetSize + parameters.channels) false ++
    EnumerationDriverCode.jump width seek

/-- Complete resident seek block, independent of the current prefix. -/
def code (parameters : Parameters) (width packetSize halt seekForced seekTry seek : Nat) :
    List (Instruction width 8) :=
  headCode width packetSize halt seekTry ++ tailCode parameters width packetSize seek seekForced

/-- Preserve the forced baseline bit, clear its false flag and resume seek. -/
def forcedSkipCode (width packetSize channels seek : Nat) : List (Instruction width 8) :=
  EnumerationMaskWrite.code width (packetSize + channels) false ++ EnumerationDriverCode.jump width seek

theorem set_self_of_getElem? {α : Type} (words : List α) (index : Nat) (value : α)
    (cell : words[index]? = some value) : words.set index value = words := by
  apply List.ext_getElem?
  intro position
  rw [List.getElem?_set]
  by_cases same : index = position
  · subst position
    have inside : index < words.length := (List.getElem?_eq_some_iff.mp cell).1
    simpa [inside] using cell.symm
  · simp [same]

private theorem seek_flag_false_at (parameters : Parameters) (width cursor : Nat)
    (previous : Finset (Fin parameters.channels)) (lower : cursor < parameters.channels)
    (member : (⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous) :
    (EnumerationMasks.maskList width parameters.buses parameters.bridge.target (cursor + 1)
      (fixedTrue (cursor + 1) previous))[parameters.channels + cursor]? = some (boolWord width false) := by
  have absent : (⟨cursor, lower⟩ : Fin parameters.channels) ∉
      fixedFalse (cursor + 1) (fixedTrue (cursor + 1) previous) := by
    intro inFalse
    have falseSpec := (EnumerationMasks.mem_fixedFalse (cursor + 1)
      (fixedTrue (cursor + 1) previous) ⟨cursor, lower⟩).mp inFalse
    have trueSpec := (EnumerationMasks.mem_fixedTrue (cursor + 1) previous ⟨cursor, lower⟩).mpr
      ⟨member, by omega⟩
    exact falseSpec.2 trueSpec
  unfold EnumerationMasks.maskList
  simpa [absent] using EnumerationMasks.masksOf_getElem?_flag width
    (extensionBase parameters.buses parameters.bridge.target
      (fixedTrue (cursor + 1) (fixedTrue (cursor + 1) previous)))
    (fixedFalse (cursor + 1) (fixedTrue (cursor + 1) previous)) ⟨cursor, lower⟩

@[simp] theorem headCode_length : (headCode width packetSize halt seekTry).length = 9 := by
  simp [headCode, EnumerationDriverCode.readBit, EnumerationCounter.code, SharedTagCompare.code_size]

theorem seek_read_word (parameters : Parameters) (width cursor : Nat)
    (previous : Finset (Fin parameters.channels)) (lower : cursor < parameters.channels)
    (forced : parameters.buses = 1 → parameters.bridge.target ∈ previous) :
    (EnumerationMasks.maskList width parameters.buses parameters.bridge.target (cursor + 1)
      (fixedTrue (cursor + 1) previous))[cursor]'(by simp [EnumerationMasks.maskList_length]; omega) =
      boolWord width (decide ((⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous)) := by
  have cell := EnumerationMasks.seek_read width parameters.buses parameters.bridge.target cursor previous lower forced
  rw [List.getElem?_eq_getElem (by simp [EnumerationMasks.maskList_length]; omega)] at cell
  exact Option.some.inj cell

section
variable (parameters : Parameters) (graph : DAG parameters.channels)
  (retained entry : Nat) (rows : List ForestIndexedOperands.Row) (roots : List Nat)
  (program : Program (EnumerationPrefixOracle.Width parameters graph retained) 8)
  (context : Context parameters graph retained entry rows roots program)
local notation "w" => EnumerationPrefixOracle.Width parameters graph retained
local notation "l" => EnumerationDriverCode.labels parameters graph w entry
local notation "packet" => EnumerationPrefixOracle.packet parameters w rows roots
include context

omit context in
theorem physical_forced_skip (present : SharedRootRead.BlockAt program entry
    (EnumerationDriverCode.code parameters graph w entry rows roots)) :
    SharedRootRead.BlockAt program (l).seekForced
      (forcedSkipCode w (SharedDetectorPrepared.packetSize graph) parameters.channels (l).seek) := by
  have found := EnumerationDriverLayout.physical parameters graph w entry rows roots program present 12 (by decide)
  simpa [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, forcedSkipCode,
    EnumerationDriverCode.labels, EnumerationDriverCode.jump, EnumerationMaskWrite.code,
    List.append_assoc] using found

theorem forced_skip_entry (previous : Finset (Fin parameters.channels)) (cursor : Nat)
    (lower : cursor < parameters.channels) (one : parameters.buses = 1)
    (targetEq : parameters.bridge.target.val = cursor)
    (forced : parameters.buses = 1 → parameters.bridge.target ∈ previous)
    (state : State w 8)
    (ready : Ready parameters packet (cursor + 1) cursor
      (fixedTrue (cursor + 1) previous) state)
    (position : state.pc = word w (l).seekForced) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      Ready parameters packet cursor cursor (fixedTrue cursor previous) final ∧
      final.pc = word w (l).seek ∧ final.output = state.output := by
  have packetSize : (packet).size = SharedDetectorPrepared.packetSize graph :=
    SharedDetectorPrepared.packet_size graph rows roots context.matched context.rootMatches
      (assignmentOfSet {parameters.bridge.target})
  let oldMasks := EnumerationMasks.maskList w parameters.buses parameters.bridge.target (cursor + 1)
    (fixedTrue (cursor + 1) previous)
  have channelEq : (⟨cursor, lower⟩ : Fin parameters.channels) = parameters.bridge.target :=
    Fin.ext targetEq.symm
  have member : (⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous := by
    rw [channelEq]
    exact forced one
  have flagCell := seek_flag_false_at parameters w cursor previous lower member
  have noFlagWrite : oldMasks.set (parameters.channels + cursor) (boolWord w false) = oldMasks :=
    set_self_of_getElem? oldMasks (parameters.channels + cursor) (boolWord w false)
      (by simpa only [oldMasks] using flagCell)
  have semanticOr := EnumerationMasks.seek_skip_forced w parameters.buses parameters.bridge.target
    cursor previous lower one targetEq
  have semantic : EnumerationMasks.maskList w parameters.buses parameters.bridge.target cursor
      (fixedTrue cursor previous) = oldMasks := by
    rcases semanticOr with same | absent
    · exact same.symm
    · exact False.elim (absent member)
  have finalMasks : oldMasks.set (parameters.channels + cursor) (boolWord w false) =
      EnumerationMasks.maskList w parameters.buses parameters.bridge.target cursor (fixedTrue cursor previous) := by
    rw [noFlagWrite]
    exact semantic.symm
  have forcedAt := physical_forced_skip parameters graph retained entry rows roots program context.present
  have writeAt : SharedRootRead.BlockAt program (l).seekForced
      (EnumerationMaskWrite.code w ((packet).size + parameters.channels) false ++
        EnumerationDriverCode.jump w (l).seek) := by
    simpa only [forcedSkipCode, ← packetSize] using forcedAt
  have writeHead := block_left program (l).seekForced
    (EnumerationMaskWrite.code w ((packet).size + parameters.channels) false)
    (EnumerationDriverCode.jump w (l).seek) writeAt
  have jumpAt := block_right program (l).seekForced
    (EnumerationMaskWrite.code w ((packet).size + parameters.channels) false)
    (EnumerationDriverCode.jump w (l).seek) writeAt
  have room := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 12 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ,
    List.getElem_cons_zero, List.length_append, EnumerationMaskWrite.code_length,
    EnumerationDriverCode.jump, List.length_cons, List.length_nil] at room
  have heapFits : state.heap.size < 2 ^ w := by
    simpa [ready.heap, Array.size_append, List.size_toArray, EnumerationMasks.maskList_length] using context.heapFits
  have inside : parameters.channels + cursor < oldMasks.length := by
    simp only [oldMasks, EnumerationMasks.maskList_length]
    omega
  obtain ⟨updated, first, heap, stack, output, pc, running, frame⟩ :=
    EnumerationDriverMask.write_execution program state (l).seekForced parameters.channels cursor packet oldMasks false
      position ready.running ready.counter inside ready.heap heapFits (by omega) writeHead
  obtain ⟨final, second, finalPC, finalHeap, finalStack, finalOutput, finalRunning, finalFrame⟩ :=
    EnumerationSteps.jump_execution (program := program) updated ((l).seekForced + 4) (l).seek pc running room
      (by simpa [EnumerationDriverCode.jump] using jumpAt 0 (by simp [EnumerationDriverCode.jump]))
      (by simpa [EnumerationDriverCode.jump] using jumpAt 1 (by simp [EnumerationDriverCode.jump]))
  have updatedSize : updated.heap.size = state.heap.size := by
    simp only [heap, ready.heap, Array.size_append, List.size_toArray, List.length_set, oldMasks]
  have updatedLive : updated.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [updatedSize, stack, output]
  have joined := first.append second
  have finalReady : Ready parameters packet cursor cursor (fixedTrue cursor previous) final := by
    refine ⟨?_, (finalFrame 3 (by decide)).trans ((frame 3 (by decide) (by decide)).trans ready.counter),
      finalStack.trans (stack.trans ready.stack), finalRunning⟩
    calc
      final.heap = updated.heap := finalHeap
      _ = packet ++ (oldMasks.set (parameters.channels + cursor) (boolWord w false)).toArray := heap
      _ = packet ++ (EnumerationMasks.maskList w parameters.buses parameters.bridge.target cursor
          (fixedTrue cursor previous)).toArray := by rw [finalMasks]
  refine ⟨final, ?_, finalReady, finalPC, finalOutput.trans output⟩
  rw [updatedLive, Nat.max_self] at joined
  simpa only [Nat.add_assoc, Nat.reduceAdd] using joined

omit context in
theorem physical (present : SharedRootRead.BlockAt program entry
    (EnumerationDriverCode.code parameters graph w entry rows roots)) :
    SharedRootRead.BlockAt program (l).seek
      (code parameters w (SharedDetectorPrepared.packetSize graph) (l).halt
        (l).seekForced (l).seekTry (l).seek) := by
  have found := EnumerationDriverLayout.physical parameters graph w entry rows roots program present 11 (by decide)
  simpa [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, code, headCode, tailCode,
    EnumerationDriverCode.readBit, EnumerationDriverCode.jump, EnumerationDriverCode.labels,
    EnumerationCounter.code, EnumerationMaskWrite.code, List.append_assoc] using found

set_option maxHeartbeats 2000000 in
theorem read_entry (previous : Finset (Fin parameters.channels)) (cursor : Nat)
    (lower : cursor < parameters.channels)
    (forced : parameters.buses = 1 → parameters.bridge.target ∈ previous)
    (state : State w 8)
    (ready : Ready parameters packet (cursor + 1) (cursor + 1)
      (fixedTrue (cursor + 1) previous) state)
    (position : state.pc = word w (l).seek) :
    ∃ observed, Execution program state observed 9 state.liveWords ∧
      Ready parameters packet (cursor + 1) cursor (fixedTrue (cursor + 1) previous) observed ∧
      observed.reg 1 = boolWord w (decide ((⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous)) ∧
      observed.pc = word w (if (⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous then (l).seek + 9 else (l).seekTry) ∧
      observed.output = state.output := by
  have packetSize : (packet).size = SharedDetectorPrepared.packetSize graph :=
    SharedDetectorPrepared.packet_size graph rows roots context.matched context.rootMatches
      (assignmentOfSet {parameters.bridge.target})
  have wholeAt := physical parameters graph retained entry rows roots program context.present
  have headAt : SharedRootRead.BlockAt program (l).seek
      (headCode w (SharedDetectorPrepared.packetSize graph) (l).halt (l).seekTry) :=
    block_left program (l).seek (headCode w (SharedDetectorPrepared.packetSize graph) (l).halt (l).seekTry)
      (tailCode parameters w (SharedDetectorPrepared.packetSize graph) (l).seek (l).seekForced) wholeAt
  have compareAt : SharedRootRead.BlockAt program (l).seek (SharedTagCompare.code w (l).halt 0 3).toList := by
    simpa [headCode, List.append_assoc] using
      block_left program (l).seek (SharedTagCompare.code w (l).halt 0 3).toList
        (EnumerationCounter.code w (2 ^ w - 1) ++ EnumerationDriverCode.readBit w (SharedDetectorPrepared.packetSize graph) ++
          [.branchZero 1 (word w (l).seekTry)]) headAt
  have compareTailAtRaw := block_right program (l).seek (SharedTagCompare.code w (l).halt 0 3).toList
    (EnumerationCounter.code w (2 ^ w - 1) ++ EnumerationDriverCode.readBit w (SharedDetectorPrepared.packetSize graph) ++
      [.branchZero 1 (word w (l).seekTry)]) headAt
  have compareTailAt : SharedRootRead.BlockAt program ((l).seek + 3)
      (EnumerationCounter.code w (2 ^ w - 1) ++ EnumerationDriverCode.readBit w (SharedDetectorPrepared.packetSize graph) ++
        [.branchZero 1 (word w (l).seekTry)]) := by
    simpa only [Array.length_toList, SharedTagCompare.code_size] using compareTailAtRaw
  have counterAt : SharedRootRead.BlockAt program ((l).seek + 3) (EnumerationCounter.code w (2 ^ w - 1)) :=
    block_left program ((l).seek + 3) (EnumerationCounter.code w (2 ^ w - 1))
      (EnumerationDriverCode.readBit w (SharedDetectorPrepared.packetSize graph) ++
        [.branchZero 1 (word w (l).seekTry)]) compareTailAt
  have readTailAtRaw := block_right program ((l).seek + 3) (EnumerationCounter.code w (2 ^ w - 1))
    (EnumerationDriverCode.readBit w (SharedDetectorPrepared.packetSize graph) ++
      [.branchZero 1 (word w (l).seekTry)]) compareTailAt
  have readTailAt : SharedRootRead.BlockAt program ((l).seek + 5)
      (EnumerationDriverCode.readBit w (SharedDetectorPrepared.packetSize graph) ++
        [.branchZero 1 (word w (l).seekTry)]) := by
    simpa only [EnumerationCounter.code_length, Nat.add_assoc, Nat.reduceAdd] using readTailAtRaw
  have readAt : SharedRootRead.BlockAt program ((l).seek + 5)
      (EnumerationDriverCode.readBit w (SharedDetectorPrepared.packetSize graph)) :=
    block_left program ((l).seek + 5) (EnumerationDriverCode.readBit w (SharedDetectorPrepared.packetSize graph))
      [.branchZero 1 (word w (l).seekTry)] readTailAt
  have readAtPacket : SharedRootRead.BlockAt program ((l).seek + 5)
      (EnumerationDriverCode.readBit w (packet).size) := by
    simpa only [← packetSize] using readAt
  have readTailAtPacket : SharedRootRead.BlockAt program ((l).seek + 5)
      (EnumerationDriverCode.readBit w (packet).size ++ [.branchZero 1 (word w (l).seekTry)]) := by
    simpa only [← packetSize] using readTailAt
  have branchAt : program[(l).seek + 8]? = some (.branchZero 1 (word w (l).seekTry)) := by
    have tailRaw := block_right program ((l).seek + 5) (EnumerationDriverCode.readBit w (packet).size)
      [.branchZero 1 (word w (l).seekTry)] readTailAtPacket
    have tail : SharedRootRead.BlockAt program ((l).seek + 8) [.branchZero 1 (word w (l).seekTry)] := by
      simpa [EnumerationDriverCode.readBit] using tailRaw
    have fetched := tail 0 (by simp)
    simpa using fetched
  have headRoom := EnumerationDriverBounds.block_room parameters graph w entry rows roots context.room 11 (by decide)
  simp only [EnumerationDriverLayout.entries, EnumerationDriverCode.chunks, List.getElem_cons_succ,
    List.getElem_cons_zero, List.length_append, Array.length_toList, SharedTagCompare.code_size,
    EnumerationCounter.code_length, EnumerationDriverCode.readBit, List.length_cons, List.length_nil,
    EnumerationDriverCode.jump, EnumerationMaskWrite.code_length] at headRoom
  have prefixRoom : (l).seek + 9 < 2 ^ w := by
    by_cases one : parameters.buses = 1 <;> simp [one] at headRoom <;> omega
  have cursorFits : cursor + 1 < 2 ^ w := by
    have fit := channels_fit parameters graph retained entry rows roots program context
    omega
  let maskWords := EnumerationMasks.maskList w parameters.buses parameters.bridge.target (cursor + 1)
    (fixedTrue (cursor + 1) previous)
  have compareCode : CodeAt program (l).seek (SharedTagCompare.code w (l).halt 0 3) := by
    intro phase
    simpa only [Array.getElem?_toList] using compareAt phase.val (by simpa using phase.isLt)
  obtain ⟨tested, first, heap, stack, output, testPC, running, frame⟩ :=
    SharedTagCompare.execution program state (l).seek (l).halt 0 (cursor + 1) 3 (by decide)
      position ready.running (by omega) (by omega) cursorFits ready.counter compareCode
  have afterTest : tested.pc = word w ((l).seek + 3) := by
    simpa only [ite_eq_right (by omega : cursor + 1 ≠ 0), Nat.add_assoc, Nat.reduceAdd] using testPC
  obtain ⟨decremented, second, counter, decHeap, decStack, decOutput, decPC, decRunning, decFrame⟩ :=
    EnumerationCounter.decrement_execution program tested ((l).seek + 3) cursor afterTest running
      ((frame 3 (by decide)).trans ready.counter) cursorFits (by omega) counterAt
  have afterDecrement : decremented.pc = word w ((l).seek + 5) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using decPC
  have masks : (EnumerationMasks.maskList w parameters.buses parameters.bridge.target (cursor + 1)
      (fixedTrue (cursor + 1) previous)) =
      maskWords := rfl
  have decrementedHeap : decremented.heap = packet ++ maskWords.toArray :=
    decHeap.trans (heap.trans ready.heap)
  have decrementedHeapFits : decremented.heap.size < 2 ^ w := by
    rw [decrementedHeap]
    simpa [maskWords, Array.size_append, List.size_toArray, EnumerationMasks.maskList_length] using context.heapFits
  obtain ⟨read, third, value, readHeap, readStack, readOutput, readPC, readRunning, readFrame⟩ :=
    EnumerationDriverMask.read_execution program decremented ((l).seek + 5) 0 cursor packet maskWords
      afterDecrement decRunning counter (by simp [maskWords, EnumerationMasks.maskList_length]; omega)
      decrementedHeap decrementedHeapFits
      (by omega) readAtPacket
  have afterRead : read.pc = word w ((l).seek + 8) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using readPC
  have cellValue : maskWords[cursor]'(by simp [maskWords, EnumerationMasks.maskList_length]; omega) =
      boolWord w (decide ((⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous)) := by
    simpa [maskWords] using seek_read_word parameters w cursor previous lower forced
  have readValue : read.reg 1 = boolWord w (decide ((⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous)) := by
    have indexValue : read.reg 1 = maskWords[cursor]'(by simp [maskWords, EnumerationMasks.maskList_length]; omega) := by
      simpa only [Nat.zero_add] using value
    exact indexValue.trans cellValue
  have oneFits : 1 < 2 ^ w := by
    have fit := channels_fit parameters graph retained entry rows roots program context
    have positive := parameters.bridge.target.isLt
    omega
  have testedLive : tested.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [heap, stack, output]
  have decrementedLive : decremented.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [decHeap, decStack, decOutput, heap, stack, output]
  by_cases member : (⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous
  · have bit : (boolWord w (decide ((⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous))).val ≠ 0 := by
      rw [boolWord_val w oneFits]
      simp [member]
    obtain ⟨final, fourth, pc, branchHeap, branchStack, branchOutput, branchRunning, branchFrame⟩ :=
      EnumerationSteps.branch_skipped (program := program) read ((l).seek + 8) (l).seekTry 1 afterRead readRunning
        (by omega) (by rw [readValue]; exact bit) branchAt
    have readLive : read.liveWords = state.liveWords := by
      unfold State.liveWords
      rw [readHeap, readStack, readOutput, decHeap, decStack, decOutput, heap, stack, output]
    have joined := first.append (second.append (third.append fourth))
    refine ⟨final, ?_, ?_, ?_, ?_, branchOutput.trans (readOutput.trans (decOutput.trans output))⟩
    · rw [testedLive, decrementedLive, readLive] at joined
      simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.max_self] using joined
    · exact ⟨branchHeap.trans (readHeap.trans (decHeap.trans (heap.trans ready.heap))),
        (branchFrame 3).trans ((readFrame 3 (by decide) (by decide)).trans counter),
        branchStack.trans (readStack.trans (decStack.trans (stack.trans ready.stack))), branchRunning⟩
    · calc
        final.reg 1 = read.reg 1 := branchFrame 1
        _ = _ := readValue
    · exact pc.trans (congrArg (word w) (ite_eq_left member).symm)
  · have bit : (boolWord w (decide ((⟨cursor, lower⟩ : Fin parameters.channels) ∈ previous))).val = 0 := by
      rw [boolWord_val w oneFits]
      simp [member]
    have readZero : (read.reg 1).val = 0 := by rw [readValue]; exact bit
    obtain ⟨final, fourth, pc, branchHeap, branchStack, branchOutput, branchRunning, branchFrame⟩ :=
      EnumerationSteps.branch_taken (program := program) read ((l).seek + 8) (l).seekTry 1 afterRead readRunning
        (by omega) readZero branchAt
    have readLive : read.liveWords = state.liveWords := by
      unfold State.liveWords
      rw [readHeap, readStack, readOutput, decHeap, decStack, decOutput, heap, stack, output]
    have joined := first.append (second.append (third.append fourth))
    refine ⟨final, ?_, ?_, ?_, ?_, branchOutput.trans (readOutput.trans (decOutput.trans output))⟩
    · rw [testedLive, decrementedLive, readLive] at joined
      simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.max_self] using joined
    · exact ⟨branchHeap.trans (readHeap.trans (decHeap.trans (heap.trans ready.heap))),
        (branchFrame 3).trans ((readFrame 3 (by decide) (by decide)).trans counter),
        branchStack.trans (readStack.trans (decStack.trans (stack.trans ready.stack))), branchRunning⟩
    · calc
        final.reg 1 = read.reg 1 := branchFrame 1
        _ = _ := readValue
    · exact pc.trans (congrArg (word w) (ite_eq_right member).symm)

end
end Controller.Cost.EnumerationDriverSeekStep
