module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroAdmissibleCaller
public import Controller.Cost.RawTransferLoops

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! A decision-only zero query for enumeration. The answer tag is saved exactly as in the
forest query, but nothing is emitted and no channel model is projected: both outcomes go
straight to the counted cleanup. Repeated oracle calls therefore leave the output stream
untouched, and per-query cost carries no native or channel-emission charge. -/
namespace Controller.Cost.EnumerationQuery
open Controller.Cost Controller.Cost.ForestZeroBackendFrame Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroAdmissibleCaller
open Controller.CNF Controller.Cost.ForestZeroCompile Controller.Cost.GateProgram Controller.Cost.ForestZeroTouch
open Controller.Cost.ForestZeroAdmissible Controller.Cost.ForestZeroEmit
open Controller.Horn.SourceDirectory Controller.Horn.SourceScan Controller.Horn.RowScan

/-- The forest answer block with its `emit` replaced by a repeated constant. -/
def quietSavedCode (width value returnPc : Nat) : Program width 8 :=
  #[.constant 0 (word width value), .constant 0 (word width value)] ++ ForestZeroAnswer.saveTagCode width ++
    #[.constant 0 (word width 0), .branchZero 0 (word width returnPc)]

def QuietSavedAt (program : Program width 8) (entry value returnPc : Nat) : Prop :=
  ∀ phase : Fin 13, program[entry + phase.val]? = (quietSavedCode width value returnPc)[phase.val]?

theorem quiet_saved_execution (program : Program width 8) (state : State width 8)
    (entry value returnPc : Nat) (count inverse localCount queryBase : Word width)
    (rest : List (Word width))
    (saved : state.stack = count :: inverse :: localCount :: queryBase :: rest)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 13 < 2 ^ width) (present : QuietSavedAt program entry value returnPc) :
    ∃ final, Execution program state final 13 (state.liveWords + 1) ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      final.stack = count :: inverse :: localCount :: queryBase :: word width value :: rest ∧
      final.reg 5 = state.reg 5 ∧
      final.pc = word width returnPc ∧ final.halted = false := by
  let first := state.advance.put 0 (word width value)
  let tagged := first.advance.put 0 (word width value)
  have pc1 : first.pc = word width (entry + 1) := by
    simpa [first, State.put] using RawTransferLoops.advance_position state position (by omega)
  have pc2 : tagged.pc = word width (entry + 2) := by
    simpa [tagged, State.put, Nat.add_assoc] using RawTransferLoops.advance_position first pc1 (by omega)
  have t0 : programStep program state = some first := by
    rw [RawTransferLoops.fetched program state entry (.constant 0 (word width value)) position (by omega)
      (by simpa [QuietSavedAt, quietSavedCode, ForestZeroAnswer.saveTagCode] using present ⟨0, by decide⟩)]
    simp [step, first, running]
  have t1 : programStep program first = some tagged := by
    rw [RawTransferLoops.fetched program first (entry + 1) (.constant 0 (word width value)) pc1 (by omega)
      (by simpa [QuietSavedAt, quietSavedCode, ForestZeroAnswer.saveTagCode] using present ⟨1, by decide⟩)]
    simp [step, first, tagged, State.put, State.advance, running]
  have taggedLive : tagged.liveWords = state.liveWords := rfl
  have firstTrace : Execution program state tagged 2 state.liveWords := by
    convert Execution.cons t0 (Execution.cons t1 (Execution.refl tagged)) using 1 <;>
      simp [first, tagged, State.liveWords, State.put, State.advance]
  have saveAt : ∀ phase : Fin 9,
      program[entry + 2 + phase.val]? = (ForestZeroAnswer.saveTagCode width)[phase.val]? := by
    intro phase
    have original := present ⟨2 + phase.val, by omega⟩
    fin_cases phase <;> simpa [quietSavedCode, ForestZeroAnswer.saveTagCode, Nat.add_assoc] using original
  obtain ⟨middle, save, heap, output, stack, reg0, reg5, pc, live⟩ :=
    ForestZeroAnswer.save_tag_execution program tagged (entry + 2) count inverse localCount queryBase rest
      (by simpa [tagged, first, State.advance, State.put] using saved)
      pc2 (by simp [tagged, first, State.advance, State.put, running]) (by omega) saveAt
  let cleared := middle.advance.put 0 (word width 0)
  let final : State width 8 := { cleared.advance with pc := word width returnPc }
  have clearPc : cleared.pc = word width (entry + 12) := by
    simpa [cleared, State.put, Nat.add_assoc] using RawTransferLoops.advance_position middle pc (by omega)
  have t11 : programStep program middle = some cleared := by
    rw [RawTransferLoops.fetched program middle (entry + 11) (.constant 0 (word width 0))
      (by simpa [Nat.add_assoc] using pc) (by omega)
      (by simpa [QuietSavedAt, quietSavedCode, ForestZeroAnswer.saveTagCode] using present ⟨11, by decide⟩)]
    simp [step, cleared, live]
  have t12 : programStep program cleared = some final := by
    rw [RawTransferLoops.fetched program cleared (entry + 12) (.branchZero 0 (word width returnPc))
      clearPc (by omega)
      (by simpa [QuietSavedAt, quietSavedCode, ForestZeroAnswer.saveTagCode] using present ⟨12, by decide⟩)]
    simp [step, cleared, final, State.advance, State.put, live, word]
  have middleLive : middle.liveWords = state.liveWords + 1 := by
    simp only [State.liveWords, heap, output, stack]
    simp [tagged, first, State.advance, State.put, State.liveWords, saved]
    omega
  have suffix : Execution program middle final 2 middle.liveWords := by
    simpa only [cleared, final, State.liveWords, State.advance, State.put, Nat.max_self,
      Nat.zero_add, Nat.reduceAdd] using Execution.cons t11 (Execution.cons t12 (Execution.refl final))
  refine ⟨final, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · simpa only [taggedLive, middleLive, Nat.reduceAdd,
      show max state.liveWords (state.liveWords + 1) = state.liveWords + 1 by omega,
      Nat.max_self] using (firstTrace.append save).append suffix
  · simpa [final, cleared, State.advance, State.put, tagged, first] using heap
  · simpa [final, cleared, State.advance, State.put, tagged, first] using output
  · simpa [final, cleared, State.advance, State.put, reg0, tagged, first] using stack
  · simpa [final, cleared, State.advance, State.put, tagged, first] using reg5
  · simp [final, cleared, State.advance, State.put, live]

/-- Save the decision tag below the four query words and release the scratch region. -/
theorem quiet_tag_cleanup (program : Program width 8) (state : State width 8)
    (entry value cleanupEntry returnPc keep count : Nat) (inverse localCount queryBase : Word width)
    (rest : List (Word width))
    (saved : state.stack = word width count :: inverse :: localCount :: queryBase :: rest)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 13 < 2 ^ width) (present : QuietSavedAt program entry value cleanupEntry)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (allocated : state.heap.size = keep + count) :
    ∃ final, Execution program state final (13 + (4 * count + 4)) (state.liveWords + 1) ∧
      final.heap.size = keep ∧ final.stack = inverse :: localCount :: queryBase :: word width value :: rest ∧
      final.output = state.output ∧ final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap := by
  obtain ⟨tagged, tagTrace, tagHeap, tagOutput, tagStack, tagFive, tagPC, tagRunning⟩ :=
    quiet_saved_execution program state entry value cleanupEntry (word width count) inverse localCount
      queryBase rest saved position running capacity present
  obtain ⟨final, cleanup, finalSize, finalStack, finalOutput, finalPC, finalRunning, lastFrame⟩ :=
    Controller.Cost.ForestZeroReclaim.stacked_execution program cleanupEntry returnPc keep count
      tagged (inverse :: localCount :: queryBase :: word width value :: rest) cleanupSetup cleanupLoop
      tagPC tagRunning cleanupCapacity countFits tagStack (by rw [tagHeap]; exact allocated)
  have taggedLive : tagged.liveWords = state.liveWords + 1 := by
    unfold State.liveWords
    rw [tagHeap, tagStack, tagOutput, saved]
    simp only [List.length_cons]
    omega
  have tagFrame : PrefixFrame keep state.heap tagged.heap := by
    simpa only [tagHeap] using ForestZeroBackendFrame.refl state.heap (by omega)
  refine ⟨final, ?_, finalSize, finalStack, finalOutput.trans tagOutput, finalPC, finalRunning,
    ForestZeroBackendFrame.trans tagFrame lastFrame⟩
  simpa only [taggedLive, Nat.max_self] using tagTrace.append cleanup

/-- Decision-only counterpart of the forest's initialized saved query: no projection, no
emission; both outcomes leave the output unchanged and return through cleanup. -/
theorem quiet_initialized_execution
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored ([] : List (Fin dictionary.coordinates.size)) base state.heap)
    (separated : base + 5 * dictionary.coordinates.size + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (cleanupEntry returnPc : Nat)
    (successAt : QuietSavedAt program fifoDone 1 cleanupEntry)
    (conflictAt : QuietSavedAt program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 13 < 2 ^ width)
    (conflictCapacity : conflict + 13 < 2 ^ width)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (count : Nat) (countFits : count < 2 ^ width)
    (inverse localCount queryBase : Word width) (rest : List (Word width))
    (savedCount : state.stack = word width count :: inverse :: localCount :: queryBase :: rest)
    (allocated : state.heap.size = keep + count) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        26 * dictionary.coordinates.size + 4 * count + 41 ∧
      peak ≤ state.liveWords + 1 ∧ final.heap.size = keep ∧
      final.stack = inverse :: localCount :: queryBase :: word width (if answer then 1 else 0) :: rest ∧
      final.output = state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) := by
  obtain ⟨queue, middle, firstTicks, firstBound, first, middleSize,
      middleStack, middleOutput, firstFrame, outcome⟩ :=
    Controller.Cost.ForestZeroOutcome.initialized_original_execution keep formula dual
      recordHeader recordStart recordEnd base entry scan seedDone conflict state program
      physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity
      fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt
      fetchCapacity advanceCapacity bucketCapacity readyCapacity
  have middleLive : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [middleSize, middleStack, middleOutput]
  rcases outcome with ⟨pc, live, noModels⟩ | ⟨fired, finished, model, forced⟩
  · obtain ⟨final, tail, finalSize, finalStack, finalOutput, finalPC, finalRunning, lastFrame⟩ :=
      quiet_tag_cleanup program middle conflict 0 cleanupEntry returnPc keep count inverse localCount queryBase
        rest (middleStack.trans savedCount) pc live conflictCapacity conflictAt cleanupSetup cleanupLoop
        cleanupCapacity countFits (by rw [middleSize]; exact allocated)
    refine ⟨false, final, firstTicks + (13 + (4 * count + 4)), max state.liveWords (middle.liveWords + 1),
      first.append tail, by omega, by rw [middleLive]; omega, finalSize, by simpa using finalStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, ForestZeroBackendFrame.trans firstFrame lastFrame, ?_⟩
    constructor
    · intro impossible; cases impossible
    · intro possible; exact False.elim (noModels possible)
  · obtain ⟨final, tail, finalSize, finalStack, finalOutput, finalPC, finalRunning, lastFrame⟩ :=
      quiet_tag_cleanup program middle fifoDone 1 cleanupEntry returnPc keep count inverse localCount queryBase
        rest (middleStack.trans savedCount) finished.position finished.running successCapacity successAt
        cleanupSetup cleanupLoop cleanupCapacity countFits (by rw [middleSize]; exact allocated)
    refine ⟨true, final, firstTicks + (13 + (4 * count + 4)), max state.liveWords (middle.liveWords + 1),
      first.append tail, by omega, by rw [middleLive]; omega, finalSize, by simpa using finalStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, ForestZeroBackendFrame.trans firstFrame lastFrame,
      ⟨fun _ => ⟨Controller.Horn.WorklistOutcome.offAssignment queue, model⟩, fun _ => rfl⟩⟩

/-- The quiet query followed by the forest's retained-dictionary reset and decision recovery:
returns with an empty represented dictionary, the decision in register 4 and the output untouched. -/
theorem quiet_reset_execution {channels ambient : Nat}
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (physical : Controller.Horn.IndexScan.PhysicalIndex (formula.clauses.toList) recordStart recordEnd base
      (Controller.Horn.IndexScan.occurrences (formula.clauses.toList) recordStart).length state.heap)
    (header : Controller.Horn.SourceScan.CursorStored recordEnd recordHeader state.heap)
    (fifo : Controller.Horn.WorklistMark.Stored ([] : List (Fin dictionary.coordinates.size)) base state.heap)
    (separated : base + 5 * dictionary.coordinates.size + 4 ≤ recordStart)
    (setupAt : ∀ phase : Fin 10, program[entry + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (zero : state.reg 2 = word width 0) (one : state.reg 5 = word width 1)
    (room : state.heap.size < 2 ^ width) (setupCapacity : entry + 10 < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (cleanupEntry returnPc : Nat)
    (successAt : QuietSavedAt program fifoDone 1 cleanupEntry)
    (conflictAt : QuietSavedAt program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 13 < 2 ^ width)
    (conflictCapacity : conflict + 13 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes count : Nat)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (rest : List (Word width))
    (savedCount : state.stack = word width count :: word width layout.inverseBase ::
      word width dictionary.coordinates.size :: word width base :: rest)
    (allocated : state.heap.size = keep + count)
    (tablePositive : 0 < layout.tableBase)
    (resetCapacity : returnPc + 27 < 2 ^ width)
    (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
    (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15)))
    (decisionCapacity : returnPc + 28 < 2 ^ width)
    (decisionAt : program[returnPc + 27]? = some (.pop 4)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 36 * formula.clauses.toList.length +
        32 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        38 * dictionary.coordinates.size + 4 * count + 58 ∧
      peak ≤ state.liveWords + 1 ∧
      final.heap.size = keep ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width (returnPc + 28) ∧ final.halted = false ∧
      PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width layout.tableBase ∧
      final.reg 2 = word width layout.inverseBase ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) := by
  obtain ⟨answer, reclaimed, firstTicks, firstPeak, first, timeBound, spaceBound,
      reclaimedSize, reclaimedStack, reclaimedOutput, reclaimedPC, reclaimedRunning,
      reclaimedFrame, meaning⟩ :=
    quiet_initialized_execution dictionary keep formula dual
      recordHeader recordStart recordEnd base entry scan seedDone conflict state program
      physical header fifo separated setupAt scanAt position running zero one room
      setupCapacity scanCapacity prefixBound prefixBelow fetch headAt headCapacity fifoDone
      bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity
      bucketCapacity readyCapacity cleanupEntry returnPc successAt conflictAt
      successCapacity conflictCapacity cleanupSetup cleanupLoop cleanupCapacity count countFits
      _ _ _ rest savedCount allocated
  let reclaimedLayout := retainedDictionaryLayout state.heap reclaimed.heap keep layout
    reclaimedFrame tableBefore inverseBefore
  have reclaimedDictionary : Represented reclaimed.heap reclaimedLayout dictionary :=
    dictionary_prefix_transport state.heap reclaimed.heap keep layout dictionary represented
      reclaimedFrame tableBefore inverseBefore
  obtain ⟨channelHeader, nodeHeader⟩ := projection_headers_transport state.heap reclaimed.heap
    keep channels nodes reclaimedFrame headersBefore channelsCell nodesCell
  obtain ⟨resetFinal, reset, finalHeap, finalStack, finalOutput, finalPC, finalRunning,
      resetFrame, zeroSlots, finalZero, finalTable, finalInverse⟩ :=
    retained_dictionary_reset_registers_execution program reclaimed returnPc channels nodes dictionary
      reclaimedLayout reclaimedDictionary ambientEq adjacent tablePositive (word width base)
      (word width (if answer then 1 else 0) :: rest) reclaimedStack reclaimedPC reclaimedRunning channelHeader nodeHeader
      (by rw [reclaimedSize]; exact headersBefore)
      (by rw [reclaimedSize]; omega) resetCapacity resetPrepareAt resetLoopAt
  have sourceBound : layout.tableBase ≤ keep := by omega
  have sourceFrame : PrefixFrame layout.tableBase state.heap reclaimed.heap :=
    ⟨by omega, by rw [reclaimedSize]; omega,
      fun address below => reclaimedFrame.2.2 address (lt_of_lt_of_le below sourceBound)⟩
  have reclaimedLive : reclaimed.liveWords ≤ firstPeak := first.final_storage_le
  obtain ⟨final, recover, decision, recoverHeap, recoverStack, recoverOutput, recoverPC,
      recoverRunning, recoverRegisters⟩ :=
    decision_recover_execution program resetFinal (returnPc + 27)
      (word width (if answer then 1 else 0)) rest finalStack finalPC finalRunning
      (by omega) decisionAt
  have resetLive : resetFinal.liveWords ≤ reclaimed.liveWords := reset.final_storage_le
  have recoverFrame : PrefixFrame layout.tableBase resetFinal.heap final.heap := by
    simpa only [recoverHeap] using ForestZeroBackendFrame.refl resetFinal.heap
      (by rw [finalHeap, Controller.Cost.ForestZeroReset.resetHeap_size, reclaimedSize]; omega)
  refine ⟨answer, final, firstTicks + (12 * dictionary.coordinates.size + 16) + 1,
    max (max firstPeak reclaimed.liveWords) resetFinal.liveWords,
    (first.append reset).append recover, ?_, ?_, ?_, recoverStack,
    recoverOutput.trans (finalOutput.trans reclaimedOutput), ?_, recoverRunning,
    ForestZeroBackendFrame.trans sourceFrame (ForestZeroBackendFrame.trans resetFrame recoverFrame),
    ?_, decision, ?_, ?_, ?_, meaning⟩
  · omega
  · omega
  · rw [recoverHeap, finalHeap, Controller.Cost.ForestZeroReset.resetHeap_size, reclaimedSize]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using recoverPC
  · have tableScalar : reclaimedLayout.tableBase = layout.tableBase := rfl
    simpa only [recoverHeap, tableScalar] using zeroSlots
  · exact (recoverRegisters 0 (by decide)).trans finalZero
  · exact (recoverRegisters 1 (by decide)).trans finalTable
  · exact (recoverRegisters 2 (by decide)).trans finalInverse

/-- Normalization, indexing and the quiet query on the scratch region; no projection or emission. -/
theorem quiet_scratch_indexed_execution {channels ambient : Nat}
    (dictionary : Dictionary ambient) (keep : Nat)
    (formula : Controller.CNF.Formula (Fin dictionary.coordinates.size)) (dual : Controller.Horn.DualHorn formula)
    (recordHeader recordStart recordEnd base entry scan seedDone conflict : Nat)
    (state : State width 8) (program : Program width 8)
    (backend : Controller.Horn.SourceDirectory.Layout formula.clauses.toList)
    (sourceStored : Stored formula.clauses.toList backend.directory backend.source state.heap)
    (directoryCursor : CursorStored backend.directory backend.directoryHeader state.heap)
    (directoryEnd : CursorStored (backend.directory + 2 * formula.clauses.toList.length) backend.endHeader state.heap)
    (baseEq : backend.base = state.heap.size) (recordHeaderEq : backend.recordHeader = keep)
    (headerEq : recordHeader = backend.recordHeader) (backendBaseEq : base = backend.base)
    (recordStartEq : recordStart = state.heap.size + 5 * dictionary.coordinates.size + 4)
    (recordEndEq : recordEnd = Controller.Horn.NormalizeLoop.recordOffset formula.clauses.toList
      recordStart formula.clauses.toList.length)
    (localCount : state.reg 2 = word width dictionary.coordinates.size)
    (sourcePointer : state.reg 1 = word width state.heap.size)
    (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
    (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11))
    (headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?)
    (endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? = (scratchEndpointCode (width := width))[phase.val]?)
    (saveAt : ∀ phase : Fin 6, program[entry + 36 + phase.val]? = (saveProjectionCode (width := width))[phase.val]?)
    (normalizerAt : Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) formula.clauses.toList backend)
    (headersAbove : ∀ address ∈ [backend.recordHeader, backend.inputHeader, backend.firstHeader,
      backend.directoryHeader, backend.endHeader], backend.recordHeader ≤ address)
    (indexSaveAt : Controller.Cost.ForestZeroHeaderBridge.SaveAt program (entry + 203) recordHeader)
    (indexAt : Controller.Horn.IndexScan.At (n := dictionary.coordinates.size) program (entry + 210) base recordStart)
    (indexRestoreAt : Controller.Cost.ForestZeroHeaderBridge.RestoreAt program (entry + 242))
    (captureAt : ∀ phase : Fin 6, program[entry + 245 + phase.val]? = (Controller.Cost.ForestZeroReclaim.captureCode width)[phase.val]?)
    (fullCapacity : entry + 261 < 2 ^ width)
    (setupAt : ∀ phase : Fin 10, program[entry + 251 + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
    (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : state.heap.size + 5 * dictionary.coordinates.size + 4 +
      3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length < 2 ^ width)
    (scanCapacity : scan + 47 < 2 ^ width)
    (prefixBound : keep ≤ state.heap.size) (prefixBelow : keep ≤ base)
    (fetch : Nat)
    (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
    (headCapacity : seedDone + 4 < 2 ^ width)
    (fifoDone bucket advance ready skip : Nat)
    (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
    (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
    (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
    (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
    (fetchCapacity : fetch + 14 < 2 ^ width) (advanceCapacity : advance + 5 < 2 ^ width)
    (bucketCapacity : bucket + 12 < 2 ^ width) (readyCapacity : ready + 26 < 2 ^ width)
    (cleanupEntry returnPc : Nat)
    (successAt : QuietSavedAt program fifoDone 1 cleanupEntry)
    (conflictAt : QuietSavedAt program conflict 0 cleanupEntry)
    (successCapacity : fifoDone + 13 < 2 ^ width)
    (conflictCapacity : conflict + 13 < 2 ^ width)
    (layout : ForestZeroDictionary.Layout ambient state.heap.size)
    (represented : Represented state.heap layout dictionary)
    (nodes : Nat)
    (ambientEq : ambient = channels + nodes)
    (adjacent : layout.inverseBase = layout.tableBase + ambient)
    (tableBefore : layout.tableBase + ambient ≤ keep)
    (inverseBefore : layout.inverseBase + ambient ≤ keep)
    (headersBefore : 1 < keep)
    (channelsCell : state.heap[0]? = some (word width channels))
    (nodesCell : state.heap[1]? = some (word width nodes))
    (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
    (channelsFit : channels + 1 < 2 ^ width) (offRoom : base + 1 < 2 ^ width)
    (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
    (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
    (cleanupCapacity : cleanupEntry + 7 < 2 ^ width)
    (rest : List (Word width))
    (saved : state.stack = word width layout.inverseBase :: word width keep :: rest)
    (tablePositive : 0 < layout.tableBase)
    (resetCapacity : returnPc + 27 < 2 ^ width)
    (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
    (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15)))
    (decisionCapacity : returnPc + 28 < 2 ^ width)
    (decisionAt : program[returnPc + 27]? = some (.pop 4)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧
      ticks ≤ 63 * dictionary.coordinates.size +
        61 * (formula.clauses.toList.map List.length).sum + 125 * formula.clauses.toList.length +
        48 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        4 * (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length - keep) +
        144 ∧
      peak ≤ state.liveWords + 5 * dictionary.coordinates.size +
        3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
        2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + 8 ∧
      final.heap.size = keep ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width (returnPc + 28) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width layout.tableBase ∧
      final.reg 2 = word width layout.inverseBase ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) := by
  let incidences := (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length
  let count := recordEnd + 2 * incidences - keep
  have dualRows : ∀ index : Fin formula.clauses.toList.length, Controller.Horn.DualHornClause formula.clauses.toList[index.val] := by
    intro index
    apply dual
    have member := List.getElem_mem index.isLt
    simpa only [Array.mem_toList_iff] using member
  obtain ⟨normalized, marks, normalizeTicks, normalizePeak, normalizeTrace, complete,
      normalizedPC, normalizeTime, normalizeSpace, normalizedStack, normalizedOutput,
      normalizeFrame⟩ :=
    scratch_normalized_execution program state entry formula.clauses.toList backend sourceStored directoryCursor
      directoryEnd baseEq position running localCount sourcePointer layout.inverseBase rest
      (by simpa only [recordHeaderEq] using saved) (by omega) (by omega)
      countAt allocateAt headersAt endpointAt saveAt normalizerAt dualRows headersAbove
  have completed : Controller.Horn.NormalizeLoop.Invariant formula.clauses.toList backend recordStart formula.clauses.toList.length marks normalized := by
    simpa only [← recordStartEq] using complete
  have normalizedSize : normalized.heap.size = recordEnd := by
    exact completed.records.endpoint.trans recordEndEq.symm
  have endBound : recordEnd ≤ recordStart + 3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum := by
    have sumBound := Controller.Horn.NormalizeLoop.wordSuffix_bound formula.clauses.toList 0
    simp only [Controller.Horn.NormalizeLoop.wordSuffix, Controller.Horn.NormalizeLoop.literalSuffix,
      List.drop_zero] at sumBound
    rw [recordEndEq, Controller.Horn.NormalizeLoop.recordOffset, List.take_length]
    omega
  have keepFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep state.heap normalized.heap := by
    simpa only [recordHeaderEq] using normalizeFrame
  obtain ⟨physical, cursor, fifo⟩ := Controller.Cost.ForestZeroIndexMarks.normalized_inputs
    formula.clauses.toList backend recordStart marks normalized completed
  have baseBelow : base ≤ normalized.heap.size := by
    have lower := Controller.Horn.NormalizeLoop.recordOffset_above formula.clauses.toList recordStart formula.clauses.toList.length
    rw [← recordEndEq, ← normalizedSize] at lower
    omega
  have headerBelow : recordHeader < base := by
    have headerBound := backend.headersBefore backend.recordHeader (by simp)
    have directoryBound := backend.directoryBefore
    have sourceBound := backend.sourceBefore
    unfold Controller.Horn.SourceDirectory.sourceOffset at sourceBound
    omega
  let savedRest := word width layout.inverseBase :: word width dictionary.coordinates.size ::
    word width base :: rest
  obtain ⟨indexed, indexTrace, indexedPhysical, indexedHeader, indexedFIFO, indexedFrame,
      indexedSize, allocated, indexedStack, indexedOutput, indexedZero, indexedOne,
      indexedPC, indexedRunning⟩ :=
    Controller.Cost.ForestZeroIndexMarks.indexed_capture_inputs keep program formula.clauses.toList
      (entry + 203) recordHeader recordStart recordEnd base normalized indexSaveAt
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using indexAt)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using indexRestoreAt)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using captureAt)
      (by simpa only [normalizedSize, backendBaseEq] using physical)
      (by simpa only [normalizedSize, headerEq] using cursor)
      normalizedPC completed.input.running completed.input.zero completed.input.one
      (by omega) baseBelow headerBelow prefixBelow
      (by simpa only [backendBaseEq] using fifo) (by omega)
      (by rw [normalizedSize]; omega) savedRest
      (by simpa only [savedRest, backendBaseEq, baseEq, recordHeaderEq] using normalizedStack)
  have indexKeepFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame keep normalized.heap indexed.heap :=
    ⟨by omega, by have := indexedFrame.2.1; omega,
      fun address below => indexedFrame.2.2 address (lt_of_lt_of_le below prefixBelow)⟩
  have prefixFrame := Controller.Cost.ForestZeroBackendFrame.trans keepFrame indexKeepFrame
  let indexedLayout := retainedDictionaryLayout state.heap indexed.heap keep layout prefixFrame
    tableBefore inverseBefore
  have indexedInverse : indexedLayout.inverseBase = layout.inverseBase := rfl
  have indexedTable : indexedLayout.tableBase = layout.tableBase := rfl
  have indexedDictionary : Represented indexed.heap indexedLayout dictionary :=
    dictionary_prefix_transport state.heap indexed.heap keep layout dictionary represented prefixFrame
      tableBefore inverseBefore
  obtain ⟨indexedChannels, indexedNodes⟩ := projection_headers_transport state.heap indexed.heap keep
    channels nodes prefixFrame headersBefore channelsCell nodesCell
  have actualSize : indexed.heap.size = keep + count := by
    simpa only [count, incidences, normalizedSize] using allocated
  have indexedLive : indexed.liveWords = normalized.liveWords + 2 * incidences := by
    unfold State.liveWords
    rw [indexedSize, indexedStack, indexedOutput, normalizedStack]
    simp only [savedRest, List.length_cons, List.length_nil]
    omega
  obtain ⟨answer, final, terminalTicks, terminalPeak, terminalTrace, terminalTime,
      terminalSpace, finalSize, finalStack, finalOutput, finalPC, finalRunning, terminalFrame,
      zeroSlots, decision, finalZero, finalTable, finalInverse, meaning⟩ :=
    quiet_reset_execution dictionary keep formula dual recordHeader recordStart recordEnd
      base (entry + 251) scan seedDone conflict indexed program indexedPhysical indexedHeader indexedFIFO
      (by simpa only [backendBaseEq] using completed.recordsAbove) setupAt scanAt (by simpa only [Nat.add_assoc, Nat.reduceAdd] using indexedPC) indexedRunning
      indexedZero indexedOne (by rw [indexedSize, normalizedSize]; omega) (by omega) scanCapacity
      (by have := prefixFrame.2.1; omega) prefixBelow fetch headAt headCapacity fifoDone bucket advance
      ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity
      cleanupEntry returnPc successAt conflictAt successCapacity conflictCapacity
      indexedLayout indexedDictionary nodes count ambientEq adjacent tableBefore inverseBefore headersBefore
      indexedChannels indexedNodes cleanupSetup cleanupLoop cleanupCapacity (by unfold count; omega) rest
      (by simpa only [count, incidences, normalizedSize, savedRest, indexedInverse] using indexedStack)
      actualSize tablePositive resetCapacity resetPrepareAt resetLoopAt decisionCapacity decisionAt
  rw [indexedTable] at terminalFrame zeroSlots finalTable
  rw [indexedInverse] at finalInverse
  have indexedTime : 16 * incidences + 18 * formula.clauses.toList.length + 22 =
      16 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + 18 * formula.clauses.toList.length + 22 := rfl
  have normalizedLive : normalized.liveWords ≤ normalizePeak := normalizeTrace.final_storage_le
  refine ⟨answer, final, normalizeTicks + (16 * incidences + 18 * formula.clauses.toList.length + 22) + terminalTicks,
    max normalizePeak (max (normalized.liveWords + 2 * incidences + 1) terminalPeak),
    (by simpa only [Nat.add_assoc, incidences] using normalizeTrace.append (indexTrace.append terminalTrace)),
    ?_, ?_, finalSize, finalStack, ?_, finalPC, finalRunning, ?_, zeroSlots, decision, finalZero, finalTable, finalInverse, meaning⟩
  · dsimp only [incidences, count] at normalizeTime terminalTime ⊢
    omega
  · rw [indexedLive] at terminalSpace
    dsimp only [incidences] at normalizeSpace terminalSpace ⊢
    omega
  · simpa only [indexedOutput, normalizedOutput] using finalOutput
  · have tableBelow : layout.tableBase ≤ keep := by omega
    have sourceFrame : Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap indexed.heap :=
      ⟨by omega, by have := prefixFrame.2.1; omega,
        fun address below => prefixFrame.2.2 address (lt_of_lt_of_le below tableBelow)⟩
    exact Controller.Cost.ForestZeroBackendFrame.trans sourceFrame terminalFrame



/-- Source constructor followed by the quiet query and dictionary reset: a returning
zero-system decision with no projection and no output. -/
theorem quiet_constructor_execution {channels ambient : Nat}
    (heap : Array (Word width)) (originalLayout : Layout ambient heap.size)
    (originalDictionary : Dictionary ambient) (originalRepresentation : Represented heap originalLayout originalDictionary)
    (references : List (List (Reference ambient))) (sourceEnd nodes : Nat)
    (sourceReferences : ∀ reference ∈ references.flatten,
      Controller.Cost.ForestZeroEmit.StoredReference heap channels sourceEnd reference)
    (sourceBeforeTable : sourceEnd ≤ originalLayout.tableBase)
    (sourceBeforeInverse : sourceEnd ≤ originalLayout.inverseBase)
    (sourceBound : sourceEnd ≤ heap.size) (sourcePositive : 0 < sourceEnd)
    (sourceChannel : heap[0]? = some (word width channels))
    (sourceNodes : heap[1]? = some (word width nodes)) (ambientEq : ambient = channels + nodes)
    (adjacent : originalLayout.inverseBase = originalLayout.tableBase + ambient)
    (tablePositive : 0 < originalLayout.tableBase) (sourceHeaderRoom : 1 < sourceEnd)
    (sourceDual : Controller.Horn.DualHorn
      (ofClauses (ForestZeroAssembly.originalRows (reservedReferences references))))
    (program : Program width 8) (sourceEntry constructorEntry entry : Nat)
    (entryEq : constructorEntry = sourceEntry + 15)
    (originalCount : originalDictionary.coordinates.size = 0)
    (sourceEndpoint : heap.size = originalLayout.inverseBase + ambient)
    (initialScratch : Nat)
    (entryCapacity : sourceEntry + 15 < 2 ^ width)
    (entryAt : ∀ phase : Fin 3, program[sourceEntry + phase.val]? = (reuseEntryCode width)[phase.val]?)
    (keepAt : ForestZeroCallerWiden.WidenedBlockAt program (sourceEntry + 3) (keepCode width))
    (cursorAt : program[sourceEntry + 14]? = some (.constant 0
      (word width (heap.size + 5 + 2 * (references.length + 1)))))
    (rest output : List (Word width)) (highRegisters : Fin 8 → Word width)
    (constructorRoom : heap.size + 5 + 2 * (references.length + 1) +
      2 * references.flatten.length + 2 * ambient < 2 ^ width)
    (ambientFits : ambient + 1 < 2 ^ width)
    (constructorCapacity : constructorEntry +
      (constructorCode width constructorEntry heap.size heap.size (heap.size + 4) entry references).length < 2 ^ width)
    (constructorAt : ForestZeroCallerWiden.WidenedBlockAt program constructorEntry
      (constructorCode width constructorEntry heap.size heap.size (heap.size + 4) entry references)) :
    let within : channels ≤ ambient := by omega
    let dictionary := constructorDictionary heap originalLayout originalDictionary references
    let formula := constructorFormula heap originalLayout originalDictionary originalRepresentation.coherent references channels within
    let state := constructorState heap originalLayout originalDictionary references channels entry
      (word width heap.size :: rest) output highRegisters
    let backend := constructorFormulaBackend heap originalLayout originalDictionary originalRepresentation.coherent references channels within
    let layout := constructorDictionaryLayout heap originalLayout originalDictionary references channels
    let keep := heap.size
    let recordHeader := heap.size
    let base := state.heap.size
    let recordStart := state.heap.size + 5 * dictionary.coordinates.size + 4
    let recordEnd := Controller.Horn.NormalizeLoop.recordOffset formula.clauses.toList recordStart formula.clauses.toList.length
    ∀ (scan seedDone conflict : Nat)
      (countAt : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?)
      (allocateAt : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11))
      (headersAt : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?)
      (endpointAt : ∀ phase : Fin 5, program[entry + 31 + phase.val]? = (scratchEndpointCode (width := width))[phase.val]?)
      (saveAt : ∀ phase : Fin 6, program[entry + 36 + phase.val]? = (saveProjectionCode (width := width))[phase.val]?)
      (normalizerAt : Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) formula.clauses.toList backend)
      (indexSaveAt : Controller.Cost.ForestZeroHeaderBridge.SaveAt program (entry + 203) recordHeader)
      (indexAt : Controller.Horn.IndexScan.At (n := dictionary.coordinates.size) program (entry + 210) base recordStart)
      (indexRestoreAt : Controller.Cost.ForestZeroHeaderBridge.RestoreAt program (entry + 242))
      (captureAt : ∀ phase : Fin 6, program[entry + 245 + phase.val]? = (Controller.Cost.ForestZeroReclaim.captureCode width)[phase.val]?)
      (fullCapacity : entry + 261 < 2 ^ width)
      (setupAt : ∀ phase : Fin 10, program[entry + 251 + phase.val]? =
      (Controller.Cost.ForestZeroSeedSetup.code (n := dictionary.coordinates.size) width base recordHeader recordStart scan)[phase.val]?)
      (scanAt : Controller.Horn.WorklistSeed.At (n := dictionary.coordinates.size) program base scan seedDone conflict)
      (room : state.heap.size + 5 * dictionary.coordinates.size + 4 +
      3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
      2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length < 2 ^ width)
      (scanCapacity : scan + 47 < 2 ^ width)
      (fetch : Nat)
      (headAt : ∀ phase : Fin 4, program[seedDone + phase.val]? =
      (Controller.Horn.WorklistAccept.headSetupCode (n := dictionary.coordinates.size) width base fetch)[phase.val]?)
      (headCapacity : seedDone + 4 < 2 ^ width)
      (fifoDone bucket advance ready skip : Nat)
      (fetchAt : Controller.Horn.WorklistFIFO.FetchAt (n := dictionary.coordinates.size) program base fetch fifoDone bucket)
      (advanceAt : Controller.Horn.WorklistFIFO.AdvanceAt (n := dictionary.coordinates.size) program base advance fetch)
      (loopAt : Controller.Horn.WorklistBucketLoop.At program bucket advance ready)
      (readyAt : Controller.Horn.WorklistBucketReady.At (n := dictionary.coordinates.size) program base ready skip conflict bucket)
      (fetchCapacity : fetch + 14 < 2 ^ width)
      (advanceCapacity : advance + 5 < 2 ^ width)
      (bucketCapacity : bucket + 12 < 2 ^ width)
      (readyCapacity : ready + 26 < 2 ^ width)
      (cleanupEntry returnPc : Nat)
      (successAt : QuietSavedAt program fifoDone 1 cleanupEntry)
      (conflictAt : QuietSavedAt program conflict 0 cleanupEntry)
      (successCapacity : fifoDone + 13 < 2 ^ width)
      (conflictCapacity : conflict + 13 < 2 ^ width)
      (localFit : dictionary.coordinates.size + 1 < 2 ^ width)
      (channelsFit : channels + 1 < 2 ^ width)
      (offRoom : base + 1 < 2 ^ width)
      (cleanupSetup : ∀ phase : Fin 3, program[cleanupEntry + phase.val]? =
      (Controller.Cost.ForestZeroReclaim.setupCode width)[phase.val]?)
      (cleanupLoop : Controller.Cost.ForestZeroReclaim.At program (cleanupEntry + 3) returnPc)
      (cleanupCapacity : cleanupEntry + 7 < 2 ^ width)
      (resetCapacity : returnPc + 27 < 2 ^ width)
      (resetPrepareAt : ForestZeroCallerWiden.WidenedBlockAt program returnPc (resetPrepareCode width).toList)
      (resetLoopAt : ForestZeroCallerWiden.WidenedBlockAt program (returnPc + 15)
      (Controller.Cost.ForestZeroReset.code width (returnPc + 15)))
      (decisionCapacity : returnPc + 28 < 2 ^ width)
      (decisionAt : program[returnPc + 27]? = some (.pop 4)),
∃ answer : Bool, ∃ final ticks peak,
      Execution program
        (Controller.Cost.RegisterWiden.widenState
          (atState heap sourceEntry 0 originalLayout.tableBase originalLayout.inverseBase
            initialScratch rest output) highRegisters)
        final ticks peak ∧
      ticks ≤ 94 + 5 * references.length + 23 * references.flatten.length +
        86 * dictionary.coordinates.size +
        61 * (formula.clauses.toList.map List.length).sum + 125 * formula.clauses.toList.length +
        48 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length +
        4 * (recordEnd + 2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length - keep) +
        144 ∧
      peak ≤ max
        (18 + heap.size + 2 * (references.length + 1) + 2 * references.flatten.length +
          2 * dictionary.coordinates.size + (word width heap.size :: rest).length + output.length)
        (state.liveWords + 5 * dictionary.coordinates.size +
        3 * formula.clauses.toList.length + (formula.clauses.toList.map List.length).sum +
        2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + 8) ∧
      final.heap.size = keep ∧ final.stack = rest ∧ final.output = output ∧
      final.pc = word width (returnPc + 28) ∧ final.halted = false ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame layout.tableBase state.heap final.heap ∧
      (∀ coordinate : Fin ambient, final.heap[layout.tableBase + coordinate.val]? = some (word width 0)) ∧
      final.reg 4 = word width (if answer then 1 else 0) ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width layout.tableBase ∧
      final.reg 2 = word width layout.inverseBase ∧
      (answer = true ↔ ∃ assignment, Controller.CNF.Satisfies assignment formula) ∧
      final.liveWords ≤ (Controller.Cost.RegisterWiden.widenState
        (atState heap sourceEntry 0 originalLayout.tableBase originalLayout.inverseBase
          initialScratch rest output) highRegisters).liveWords +
        1 ∧
      Controller.Cost.ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase heap final.heap ∧
      ∃ reusableLayout : Layout ambient final.heap.size,
        reusableLayout.tableBase = originalLayout.tableBase ∧
        reusableLayout.inverseBase = originalLayout.inverseBase ∧
        Represented final.heap reusableLayout (ForestZeroCompile.empty ambient) ∧
      (∀ next : Nat, answer = false →
        QueryReady (ambient := ambient) heap originalLayout.tableBase originalLayout.inverseBase next rest
          (ForestZeroRootLoop.dispatchState final (returnPc + 28) next false)) := by
  intro within dictionary formula state backend layout keep recordHeader base recordStart recordEnd
  intro scan seedDone conflict countAt allocateAt headersAt endpointAt saveAt normalizerAt indexSaveAt indexAt indexRestoreAt captureAt fullCapacity setupAt scanAt room scanCapacity fetch headAt headCapacity fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity cleanupEntry returnPc successAt conflictAt successCapacity conflictCapacity localFit channelsFit offRoom cleanupSetup cleanupLoop cleanupCapacity resetCapacity resetPrepareAt resetLoopAt decisionCapacity decisionAt
  have actualDual : Controller.Horn.DualHorn formula :=
    constructorClauses_dualHorn heap originalLayout originalDictionary originalRepresentation.coherent
      references channels within sourceDual
  have originalInputs := constructor_canonical_inputs heap originalLayout originalDictionary
    originalRepresentation references channels within
  have actualStored : Stored formula.clauses.toList backend.directory backend.source state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.1
  have actualCursor : CursorStored backend.directory backend.directoryHeader state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.2.1
  have actualEnd : CursorStored (backend.directory + 2 * formula.clauses.toList.length) backend.endHeader state.heap := by
    simpa only [formula, state, backend, constructorState, RegisterWiden.widenState, atState,
      constructorFormulaBackend, constructorBackend, backendLayout, constructorFormula_rows] using originalInputs.2.2
  have actualBase : backend.base = state.heap.size := rfl
  have actualRecordHeader : backend.recordHeader = keep := rfl
  have actualLocalCount : state.reg 2 = word width dictionary.coordinates.size := rfl
  have actualSourcePointer : state.reg 1 = word width state.heap.size := rfl
  have actualHeadersAbove : ∀ address ∈ [backend.recordHeader, backend.inputHeader, backend.firstHeader,
      backend.directoryHeader, backend.endHeader], backend.recordHeader ≤ address := by
    intro address member
    change address ∈ [heap.size, heap.size + 1, heap.size + 2, heap.size + 3, heap.size + 4] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> change heap.size ≤ _ <;> omega
  have actualGrowth : keep ≤ state.heap.size := constructorHeap_growth heap originalLayout originalDictionary references channels
  have actualRepresented : Represented state.heap layout dictionary :=
    constructor_dictionary_represented heap originalLayout originalDictionary originalRepresentation references channels
  have actualTableBefore : layout.tableBase + ambient ≤ keep := originalLayout.tableBound
  have actualInverseBefore : layout.inverseBase + ambient ≤ keep := originalLayout.inverseBound
  have actualChannels : state.heap[0]? = some (word width channels) :=
    (constructor_source_cell heap originalLayout originalDictionary references channels sourceEnd 0
      sourceBeforeTable sourceBeforeInverse sourceBound (by omega)).trans sourceChannel
  have actualNodes : state.heap[1]? = some (word width nodes) :=
    (constructor_source_cell heap originalLayout originalDictionary references channels sourceEnd 1
      sourceBeforeTable sourceBeforeInverse sourceBound sourceHeaderRoom).trans sourceNodes
  obtain ⟨answer, final, queryTicks, queryPeak, queryTrace, queryTime, querySpace,
      heapSize, finalStack, finalOutput, finalPC, finalRunning, finalFrame, zeroTable,
      decision, zeroRegister, tableRegister, inverseRegister, meaning⟩ :=
    quiet_scratch_indexed_execution dictionary keep formula actualDual recordHeader recordStart recordEnd base entry scan seedDone conflict state program backend actualStored actualCursor actualEnd actualBase actualRecordHeader rfl rfl rfl rfl actualLocalCount actualSourcePointer countAt allocateAt headersAt endpointAt saveAt normalizerAt actualHeadersAbove indexSaveAt indexAt indexRestoreAt captureAt fullCapacity setupAt scanAt rfl rfl room scanCapacity actualGrowth actualGrowth fetch headAt headCapacity fifoDone bucket advance ready skip fetchAt advanceAt loopAt readyAt fetchCapacity advanceCapacity bucketCapacity readyCapacity cleanupEntry returnPc successAt conflictAt successCapacity conflictCapacity layout actualRepresented nodes ambientEq adjacent actualTableBefore actualInverseBefore (by omega) actualChannels actualNodes localFit channelsFit offRoom cleanupSetup cleanupLoop cleanupCapacity rest rfl tablePositive resetCapacity resetPrepareAt resetLoopAt decisionCapacity decisionAt
  obtain ⟨constructorTicks, constructorPeak, constructorTrace, constructorTime, constructorSpace⟩ :=
    constructor_state_execution program heap originalLayout originalDictionary originalRepresentation channels
      sourceEnd references sourceReferences sourceBeforeTable sourceBeforeInverse sourceBound sourcePositive
      sourceChannel within constructorEntry entry (word width heap.size :: rest) output highRegisters
      constructorRoom ambientFits constructorCapacity constructorAt
  have prepared := reuse_entry_execution program heap sourceEntry originalLayout.tableBase
    originalLayout.inverseBase initialScratch rest output highRegisters (by omega) entryAt
  have kept := keep_cursor_execution8 program heap originalLayout channels nodes (sourceEntry + 3)
    references rest output highRegisters ambientEq sourceEndpoint (by omega) sourceChannel sourceNodes
    (by omega) (by omega) keepAt (by simpa only [Nat.add_assoc] using cursorAt)
  simp only [Nat.add_assoc] at kept
  simp only [Nat.add_assoc] at constructorTrace
  rw [originalCount, entryEq] at constructorTrace
  have readyTrace := prepared.append kept
  have queryTraceAll := constructorTrace.append queryTrace
  have joined := readyTrace.append queryTraceAll
  refine ⟨answer, final, 15 + (constructorTicks + queryTicks),
    max (max (10 + heap.size + rest.length + output.length)
      (11 + heap.size + rest.length + output.length)) (max constructorPeak queryPeak),
    (by simpa only [← Nat.add_assoc] using joined), ?_, ?_, heapSize, finalStack, ?_, finalPC, finalRunning, finalFrame,
    zeroTable, decision, zeroRegister, tableRegister, inverseRegister, meaning, ?_, ?_, ?_⟩
  · simp only [dictionary, constructorDictionary] at constructorTime queryTime ⊢
    omega
  · have constructorBelow := Nat.le_max_left
        (18 + heap.size + 2 * (references.length + 1) + 2 * references.flatten.length +
          2 * dictionary.coordinates.size + (word width heap.size :: rest).length + output.length)
        (state.liveWords + 5 * dictionary.coordinates.size + 3 * formula.clauses.toList.length +
          (formula.clauses.toList.map List.length).sum +
          2 * (Controller.Horn.IndexScan.occurrences formula.clauses.toList recordStart).length + channels + 8)
    have combined := max_le_max constructorSpace querySpace
    simp only [dictionary, constructorDictionary] at constructorSpace querySpace constructorBelow combined ⊢
    simp only [List.length_cons] at constructorBelow combined ⊢
    omega
  · simpa [state, constructorState, RegisterWiden.widenState, atState] using finalOutput
  · unfold State.liveWords
    rw [heapSize, finalStack, finalOutput]
    simp [keep, state, constructorState, RegisterWiden.widenState, atState] <;> omega
  · have before := constructor_prefix heap originalLayout originalDictionary references channels adjacent
    have after : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase
        (constructorHeap heap originalLayout originalDictionary references channels) final.heap := by
      simpa only [layout, constructorDictionaryLayout, state, constructorState,
        RegisterWiden.widenState, atState] using finalFrame
    exact ForestZeroBackendFrame.trans before after
  · let reusableLayout : Layout ambient final.heap.size :=
      { tableBase := originalLayout.tableBase
        inverseBase := originalLayout.inverseBase
        tableBound := by rw [heapSize]; exact originalLayout.tableBound
        inverseBound := by rw [heapSize]; exact originalLayout.inverseBound
        disjoint := originalLayout.disjoint }
    have actualZero : ∀ coordinate : Fin ambient,
        final.heap[originalLayout.tableBase + coordinate.val]? = some (word width 0) := by
      intro coordinate
      simpa only [layout, constructorDictionaryLayout] using zeroTable coordinate
    refine ⟨reusableLayout, rfl, rfl,
      empty_dictionary_from_zero_table final.heap reusableLayout actualZero, ?_⟩
    intro next failed
    have originalFrame : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase heap final.heap := by
      have before := constructor_prefix heap originalLayout originalDictionary references channels adjacent
      have after : ForestZeroBackendFrame.PrefixFrame originalLayout.tableBase
          (constructorHeap heap originalLayout originalDictionary references channels) final.heap := by
        simpa only [layout, constructorDictionaryLayout, state, constructorState,
          RegisterWiden.widenState, atState] using finalFrame
      exact ForestZeroBackendFrame.trans before after
    exact failed_query_dispatch_ready heap originalLayout.tableBase originalLayout.inverseBase
      (returnPc + 28) next rest final heapSize originalFrame actualZero finalStack zeroRegister
      (by simpa only [layout, constructorDictionaryLayout] using tableRegister)
      (by simpa only [layout, constructorDictionaryLayout] using inverseRegister)


end Controller.Cost.EnumerationQuery
