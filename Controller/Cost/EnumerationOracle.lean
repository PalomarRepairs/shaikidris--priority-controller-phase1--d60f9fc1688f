module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationPrepared
public import Controller.Cost.SharedDetectorAssembly

@[expose] public section

/-! The enumeration oracle as a re-entrant subroutine. From the healthy packet and a pair of
fixed-channel masks it decides whether some output can be made to differ from its healthy
value, then restores the healthy packet exactly, keeps the masks for the caller and returns. -/
namespace Controller.Cost.EnumerationOracle
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

/-- A zero output count returns the negative decision at once; otherwise control continues
after the guard. Only registers 0 and 4 can change. -/
def guardCode (width entry back : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width 4), .load 0 0, .branchZero 0 (word width (entry + 5)),
    .constant 0 (word width 0), .branchZero 0 (word width (entry + 8)),
    .constant 4 (word width 0), .constant 0 (word width 0), .branchZero 0 (word width back)]

@[simp] theorem guardCode_length : (guardCode width entry back).length = 8 := rfl

theorem guard_execution (program : Program width 8) (state : State width 8) (entry back count : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 8 < 2 ^ width) (countFits : count < 2 ^ width)
    (countCell : state.heap[4]? = some (word width count))
    (present : SharedRootRead.BlockAt program entry (guardCode width entry back)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 6 ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.halted = false ∧
      (count = 0 → final.pc = word width back ∧ final.reg 4 = word width 0) ∧
      (count ≠ 0 → final.pc = word width (entry + 8) ∧
        ∀ index : Fin 8, index ≠ 0 → final.reg index = state.reg index) := by
  have fetch : ∀ offset (valid : offset < 8), program[entry + offset]? = (guardCode width entry back)[offset]? :=
    fun offset valid => present offset (by simpa using valid)
  obtain ⟨addressed, addressTrace, addressPC, addressReg, addressHeap, addressStack, addressOutput,
    addressRunning, addressFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry 4 0 state position running (by omega)
      (by simpa [guardCode] using fetch 0 (by decide))
  have bounded : (addressed.reg 0).val < addressed.heap.size := by
    rw [addressReg, addressHeap]
    have := (Array.getElem?_eq_some_iff.mp countCell).1
    simpa [word, Nat.mod_eq_of_lt (show 4 < 2 ^ width by omega)] using this
  have loadedValue : addressed.heap[(addressed.reg 0).val] = word width count := by
    have cell := countCell
    rw [← addressHeap] at cell
    have index : (addressed.reg 0).val = 4 := by
      rw [addressReg]; exact Nat.mod_eq_of_lt (by omega)
    simp only [index] at bounded ⊢
    rw [Array.getElem?_eq_getElem bounded] at cell
    exact Option.some.inj cell
  let loaded := addressed.advance.put 0 (word width count)
  have loadStep : step (.load 0 0) addressed = some loaded := by
    simp [step, addressRunning, bounded, loaded, loadedValue]
  have loadTrace := SharedDetectorSteps.single program addressed loaded (entry + 1) _ addressPC (by omega)
    (by simpa [guardCode] using fetch 1 (by decide)) loadStep
  have loadedPC : loaded.pc = word width (entry + 2) := by
    simpa [loaded, State.put] using advance_position addressed addressPC (by omega)
  have addressLive : addressed.liveWords = state.liveWords := by
    simp only [State.liveWords, addressHeap, addressStack, addressOutput]
  have loadedLive : loaded.liveWords = state.liveWords := by
    simp only [loaded, State.liveWords, State.put, State.advance] at addressLive ⊢; exact addressLive
  have branchFetch : program[entry + 2]? = some (.branchZero 0 (word width (entry + 5))) := by
    simpa [guardCode] using fetch 2 (by decide)
  have countValue : (loaded.reg 0).val = count := by
    simp [loaded, State.put, State.advance, word, Nat.mod_eq_of_lt countFits]
  have loadedRunning : loaded.halted = false := addressRunning
  by_cases emptyOutputs : count = 0
  · let jumped : State width 8 := { loaded.advance with pc := word width (entry + 5) }
    have branchStep : step (.branchZero 0 (word width (entry + 5))) loaded = some jumped := by
      simp [step, loadedRunning, jumped, countValue, emptyOutputs]
    have branchTrace := SharedDetectorSteps.single program loaded jumped (entry + 2) _ loadedPC (by omega) branchFetch branchStep
    obtain ⟨tagged, tagTrace, tagPC, tagReg, tagHeap, tagStack, tagOutput, tagRunning, tagFrame⟩ :=
      SharedEvaluationReclaim.constant_execution program (entry + 5) 0 4 jumped rfl loadedRunning (by omega)
        (by simpa [guardCode] using fetch 5 (by decide))
    obtain ⟨cleared, clearTrace, clearPC, clearReg, clearHeap, clearStack, clearOutput, clearRunning, clearFrame⟩ :=
      SharedEvaluationReclaim.constant_execution program (entry + 5 + 1) 0 0 tagged tagPC tagRunning (by omega)
        (by simpa [guardCode] using fetch 6 (by decide))
    let final : State width 8 := { cleared.advance with pc := word width back }
    have clearValue : (cleared.reg 0).val = 0 := by rw [clearReg]; simp [word]
    have jumpStep : step (.branchZero 0 (word width back)) cleared = some final := by
      simp [step, clearRunning, final, clearValue]
    have jumpTrace := SharedDetectorSteps.single program cleared final (entry + 5 + 1 + 1) _ clearPC (by omega)
      (by simpa [guardCode, Nat.add_assoc] using fetch 7 (by decide)) jumpStep
    have jumpedLive : jumped.liveWords = state.liveWords := loadedLive
    have taggedLive : tagged.liveWords = state.liveWords := by
      simp only [State.liveWords, tagHeap, tagStack, tagOutput] at jumpedLive ⊢; exact jumpedLive
    have clearedLive : cleared.liveWords = state.liveWords := by
      simp only [State.liveWords, clearHeap, clearStack, clearOutput] at taggedLive ⊢; exact taggedLive
    have finalLive : final.liveWords = state.liveWords := clearedLive
    have joined := addressTrace.append (loadTrace.append (branchTrace.append (tagTrace.append (clearTrace.append jumpTrace))))
    simp only [addressLive, loadedLive, jumpedLive, taggedLive, clearedLive, finalLive, Nat.max_self] at joined
    refine ⟨final, _, joined, by omega, ?_, ?_, ?_, clearRunning, fun _ => ⟨rfl, ?_⟩, fun nonzero => absurd emptyOutputs nonzero⟩
    · change cleared.heap = state.heap; rw [clearHeap, tagHeap]; exact addressHeap
    · change cleared.stack = state.stack; rw [clearStack, tagStack]; exact addressStack
    · change cleared.output = state.output; rw [clearOutput, tagOutput]; exact addressOutput
    · change cleared.reg 4 = word width 0; rw [clearFrame 4 (by decide)]; exact tagReg
  · let skipped := loaded.advance
    have branchStep : step (.branchZero 0 (word width (entry + 5))) loaded = some skipped := by
      simp [step, loadedRunning, skipped, countValue, emptyOutputs]
    have branchTrace := SharedDetectorSteps.single program loaded skipped (entry + 2) _ loadedPC (by omega) branchFetch branchStep
    have skippedPC : skipped.pc = word width (entry + 3) := advance_position loaded loadedPC (by omega)
    obtain ⟨cleared, clearTrace, clearPC, clearReg, clearHeap, clearStack, clearOutput, clearRunning, clearFrame⟩ :=
      SharedEvaluationReclaim.constant_execution program (entry + 3) 0 0 skipped skippedPC loadedRunning (by omega)
        (by simpa [guardCode] using fetch 3 (by decide))
    let final : State width 8 := { cleared.advance with pc := word width (entry + 8) }
    have clearValue : (cleared.reg 0).val = 0 := by rw [clearReg]; simp [word]
    have jumpStep : step (.branchZero 0 (word width (entry + 8))) cleared = some final := by
      simp [step, clearRunning, final, clearValue]
    have jumpTrace := SharedDetectorSteps.single program cleared final (entry + 4) _ (by simpa [Nat.add_assoc] using clearPC)
      (by omega) (by simpa [guardCode] using fetch 4 (by decide)) jumpStep
    have skippedLive : skipped.liveWords = state.liveWords := loadedLive
    have clearedLive : cleared.liveWords = state.liveWords := by
      simp only [State.liveWords, clearHeap, clearStack, clearOutput] at skippedLive ⊢; exact skippedLive
    have finalLive : final.liveWords = state.liveWords := clearedLive
    have joined := addressTrace.append (loadTrace.append (branchTrace.append (clearTrace.append jumpTrace)))
    simp only [addressLive, loadedLive, skippedLive, clearedLive, finalLive, Nat.max_self] at joined
    refine ⟨final, _, joined, by omega, ?_, ?_, ?_, clearRunning, fun zero => absurd zero emptyOutputs,
      fun _ => ⟨rfl, ?_⟩⟩
    · change cleared.heap = state.heap; rw [clearHeap]; exact addressHeap
    · change cleared.stack = state.stack; rw [clearStack]; exact addressStack
    · change cleared.output = state.output; rw [clearOutput]; exact addressOutput
    · intro index other
      change cleared.reg index = state.reg index
      rw [clearFrame index other]
      simp only [skipped, loaded, State.put, State.advance, ite_eq_right other]
      exact addressFrame index other

/-- Push constant words so that the first listed word ends on top. -/
def pushCode (width : Nat) : List (Word width) → List (Instruction width 8)
  | [] => []
  | value :: rest => pushCode width rest ++ [.constant 1 value, .push 1]

@[simp] theorem pushCode_length (values : List (Word width)) : (pushCode width values).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp [pushCode, ih]; omega

theorem push_execution (program : Program width 8) (values : List (Word width)) :
    ∀ (state : State width 8) (entry : Nat), state.pc = word width entry → state.halted = false →
      entry + 2 * values.length < 2 ^ width →
      SharedRootRead.BlockAt program entry (pushCode width values) →
      ∃ final, Execution program state final (2 * values.length) (state.liveWords + values.length) ∧
        final.heap = state.heap ∧ final.stack = values ++ state.stack ∧ final.output = state.output ∧
        final.pc = word width (entry + 2 * values.length) ∧ final.halted = false ∧
        (∀ index : Fin 8, index ≠ 1 → final.reg index = state.reg index) := by
  induction values with
  | nil =>
    intro state entry position running room present
    exact ⟨state, by simpa using Execution.refl (p := program) state, rfl, rfl, rfl, by simpa using position, running,
      fun _ _ => rfl⟩
  | cons value rest ih =>
    intro state entry position running room present
    simp only [List.length_cons] at room
    have restAt : SharedRootRead.BlockAt program entry (pushCode width rest) := by
      intro offset below
      have found := present offset (by simp [pushCode]; simp at below; omega)
      rwa [show pushCode width (value :: rest) = pushCode width rest ++ _ from rfl,
        List.getElem?_append_left below] at found
    obtain ⟨middle, trace, heap, stack, output, pc, active, frame⟩ :=
      ih state entry position running (by omega) restAt
    have tailAt : ∀ offset (valid : offset < 2), program[entry + 2 * rest.length + offset]? =
        ([.constant 1 value, .push 1] : List (Instruction width 8))[offset]? := by
      intro offset valid
      have found := present (2 * rest.length + offset) (by simp [pushCode]; omega)
      rw [show pushCode width (value :: rest) = pushCode width rest ++ _ from rfl,
        List.getElem?_append_right (by simp)] at found
      simpa [Nat.add_assoc] using found
    obtain ⟨loaded, loadTrace, loadPC, loadReg, loadHeap, loadStack, loadOutput, loadRunning, loadFrame⟩ :=
      SharedEvaluationReclaim.constant_execution program (entry + 2 * rest.length) value.val 1 middle pc active (by omega)
        (by simpa [word, Nat.mod_eq_of_lt value.isLt] using tailAt 0 (by decide))
    obtain ⟨pushed, pushTrace, pushPC, pushReg, pushHeap, pushStack, pushOutput, pushRunning⟩ :=
      SharedDetectorSteps.push_execution program loaded (entry + 2 * rest.length + 1) 1 loadPC loadRunning (by omega)
        (by simpa [Nat.add_assoc] using tailAt 1 (by decide))
    have loadedLive : loaded.liveWords = middle.liveWords := by simp only [State.liveWords, loadHeap, loadStack, loadOutput]
    have middleLive : middle.liveWords = state.liveWords + rest.length := by
      simp only [State.liveWords, heap, stack, output, List.length_append]; omega
    have valueWord : word width value.val = value := by
      apply Fin.ext; exact Nat.mod_eq_of_lt value.isLt
    have joined := trace.append (loadTrace.append pushTrace)
    refine ⟨pushed, ?_, by rw [pushHeap, loadHeap, heap], ?_, by rw [pushOutput, loadOutput, output], ?_, pushRunning, ?_⟩
    · convert joined using 1
      · simp only [List.length_cons]; omega
    · simp [pushStack, loadStack, loadReg, valueWord, stack]
    · rw [pushPC]; simp only [List.length_cons]; congr 1 <;> omega
    · intro index other
      rw [pushReg, loadFrame index other, frame index other]

section Code
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.ForestIndexedOperands
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.SharedDetectorPrepared
variable (parameters : Parameters) (graph : DAG parameters.channels) (T F : Finset (Fin parameters.channels))

def candidatesEntry (entry : Nat) : Nat := entry + 8

def directoryEntry (entry : Nat) : Nat :=
  candidatesEntry entry + (10 * graph.roots.length + 14 * parameters.channels + 620)

def setupEntry (entry : Nat) : Nat := directoryEntry parameters graph entry + (4 * graph.roots.length + 11)

def handoffEntry (entry : Nat) : Nat :=
  setupEntry parameters graph entry + 2 * (3 * (parameters.channels + graph.nodeCount) + 1)

def scanEntry (entry : Nat) : Nat := handoffEntry parameters graph entry + 7

/-- First instruction after the scan; the scan's own length does not depend on its return address. -/
def teardownEntry (width entry : Nat) : Nat :=
  match graph.roots.head? with
  | none => scanEntry parameters graph entry
  | some root => EnumerationLoop.returnPoint parameters graph T F (preparedSize graph) (coordinateBase graph)
      (slot graph) (scanEntry parameters graph entry) root width + 8

def scanCode (width entry : Nat) : List (Instruction width 8) :=
  match graph.roots.head? with
  | none => []
  | some root => EnumerationLoop.code parameters graph T F (Array.replicate (preparedSize graph) (word width 0))
      (layout graph _ (by simp)) (coordinateBase graph) (slot graph) graph.roots.length
      (scanEntry parameters graph entry) (teardownEntry parameters graph T F width entry) root

theorem scanCode_length (width entry : Nat) :
    scanEntry parameters graph entry + (scanCode parameters graph T F width entry).length =
      teardownEntry parameters graph T F width entry := by
  unfold scanCode teardownEntry
  split
  · simp
  · rw [EnumerationLoop.code_length]; simp

/-- The healthy singleton channel words written back by the teardown. -/
def healthyWords (width : Nat) : List (Word width) :=
  (List.finRange parameters.channels).map (fun channel =>
    boolWord width (assignmentOfSet {parameters.bridge.target} channel))

def teardownCode (width entry back : Nat) : List (Instruction width 8) :=
  (SharedEvaluationReclaim.code width (teardownEntry parameters graph T F width entry)
    (teardownEntry parameters graph T F width entry + 7)
    (2 * graph.roots.length + 3 * (parameters.channels + graph.nodeCount) + 1)).toList ++
  (pushCode width (healthyWords parameters width) ++
  (SharedChannelRewrite.code width (maskBase graph) (List.finRange parameters.channels) ++
  [.constant 0 (word width 0), .branchZero 0 (word width back)]))

@[simp] theorem teardownCode_length (width entry back : Nat) :
    (teardownCode parameters graph T F width entry back).length = 5 * parameters.channels + 9 := by
  simp [teardownCode, healthyWords, SharedEvaluationReclaim.code]; omega

/-- The complete resident oracle at `entry`, returning to `back`. -/
def code (width : Nat) (rows : List Row) (roots : List Nat) (entry back : Nat) : List (Instruction width 8) :=
  guardCode width entry back ++
    ((SharedRetainedCandidates.code width parameters.channels rows roots (candidatesEntry entry)
      (directoryEntry parameters graph entry)).toList ++
    (SharedDetectorDirectoryAlloc.code width (packetSize graph) (rootBase graph) graph.roots.length
      (directoryEntry parameters graph entry) ++
    (SharedCoordinateTable.code width (setupWords width graph (SharedDetectorAssembly.firstRoot parameters graph)) ++
    (SharedDetectorSteps.handoffCode width (tableBase graph) (inverseBase graph) graph.roots.length (packetSize graph) ++
    (scanCode parameters graph T F width entry ++ teardownCode parameters graph T F width entry back)))))

theorem code_length (width : Nat) (rows : List Row) (roots : List Nat) (entry back : Nat)
    (rootMatches : RootsMatch graph roots) :
    entry + (code parameters graph T F width rows roots entry back).length =
      teardownEntry parameters graph T F width entry + (5 * parameters.channels + 9) := by
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have scanEnd := scanCode_length parameters graph T F width entry
  simp only [code, List.length_append, Array.length_toList, SharedRetainedCandidates.code_size, rootCount,
    SharedDetectorDirectoryAlloc.code_length, SharedCoordinateTable.code_length, setupWords_length,
    guardCode_length, SharedDetectorSteps.handoffCode_length, teardownCode_length,
    scanEntry, handoffEntry, setupEntry, directoryEntry, candidatesEntry] at scanEnd ⊢
  omega

theorem teardownEntry_bound (width entry : Nat) :
    teardownEntry parameters graph T F width entry ≤ entry + 500 * (graph.countedSize + 1) + 1200 := by
  have size := graph.countedSize_eq
  have scanEnd := scanCode_length parameters graph T F width entry
  have scanBound : (scanCode parameters graph T F width entry).length ≤ 410 * (graph.countedSize + 1) + 502 := by
    unfold scanCode
    split
    · simp
    · exact EnumerationLoop.code_length_bound parameters graph T F _ _ _ _ _ _ _ _
  simp only [scanEntry, handoffEntry, setupEntry, directoryEntry, candidatesEntry] at scanEnd
  omega

end Code

theorem jump_execution (program : Program width 8) (state : State width 8) (at_ back : Nat)
    (position : state.pc = word width at_) (running : state.halted = false) (room : at_ + 2 < 2 ^ width)
    (present : SharedRootRead.BlockAt program at_ [.constant 0 (word width 0), .branchZero 0 (word width back)]) :
    ∃ final, Execution program state final 2 state.liveWords ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧ final.pc = word width back ∧
      final.halted = false ∧ (∀ index : Fin 8, index ≠ 0 → final.reg index = state.reg index) := by
  obtain ⟨cleared, clearTrace, clearPC, clearReg, clearHeap, clearStack, clearOutput, clearRunning, clearFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program at_ 0 0 state position running (by omega)
      (by simpa using present 0 (by simp))
  let final : State width 8 := { cleared.advance with pc := word width back }
  have clearValue : (cleared.reg 0).val = 0 := by rw [clearReg]; simp [word]
  have jumpStep : step (.branchZero 0 (word width back)) cleared = some final := by
    simp [step, clearRunning, final, clearValue]
  have jumpTrace := SharedDetectorSteps.single program cleared final (at_ + 1) _ clearPC (by omega)
    (by simpa using present 1 (by simp)) jumpStep
  have clearedLive : cleared.liveWords = state.liveWords := by simp only [State.liveWords, clearHeap, clearStack, clearOutput]
  have finalLive : final.liveWords = cleared.liveWords := rfl
  have joined := clearTrace.append jumpTrace
  rw [finalLive, clearedLive, Nat.max_self, Nat.max_self] at joined
  exact ⟨final, joined, clearHeap, clearStack, clearOutput, rfl, clearRunning, fun index other => clearFrame index other⟩

open Controller.Cost.ForestInputStored in
set_option maxHeartbeats 2000000 in
/-- Release a known suffix, restore the channel words and jump back. -/
theorem teardown_execution {n : Nat} (program : Program width 8) (state : State width 8) (start back : Nat)
    (retained : Array (Word width)) (values fresh : Fin n → Bool) (extra : List (Word width))
    (position : state.pc = word width start) (running : state.halted = false)
    (room : start + 5 * n + 9 < 2 ^ width) (capacity : retained.size + n < 2 ^ width)
    (extraFits : extra.length < 2 ^ width)
    (heapStored : state.heap = withValues retained values ++ extra.toArray)
    (present : SharedRootRead.BlockAt program start
      ((SharedEvaluationReclaim.code width start (start + 7) extra.length).toList ++
        (pushCode width ((List.finRange n).map (fun channel => boolWord width (fresh channel))) ++
        (SharedChannelRewrite.code width retained.size (List.finRange n) ++
        [.constant 0 (word width 0), .branchZero 0 (word width back)])))) :
    ∃ final peak, Execution program state final (4 * extra.length + 5 * n + 6) peak ∧
      peak ≤ state.liveWords + n ∧ final.heap = withValues retained fresh ∧ final.stack = state.stack ∧
      final.output = state.output ∧ final.pc = word width back ∧ final.halted = false ∧
      final.reg 4 = state.reg 4 := by
  have releaseAt : CodeAt program start (SharedEvaluationReclaim.code width start (start + 7) extra.length) :=
    SharedDetectorAssembly.block_code program _ _ (SharedDetectorAssembly.block_left program _ _ _ present)
  have afterRelease := SharedDetectorAssembly.block_right program _ _ _ present
  rw [Array.length_toList, SharedEvaluationReclaim.code_size] at afterRelease
  have pushAt := SharedDetectorAssembly.block_left program _ _ _ afterRelease
  have afterPush := SharedDetectorAssembly.block_right program _ _ _ afterRelease
  rw [pushCode_length, List.length_map, List.length_finRange] at afterPush
  have rewriteAt := SharedDetectorAssembly.block_left program _ _ _ afterPush
  have jumpAt := SharedDetectorAssembly.block_right program _ _ _ afterPush
  rw [SharedChannelRewrite.code_length, List.length_finRange] at jumpAt
  obtain ⟨released, releaseTrace, releaseHeap, releaseStack, releaseOutput, releasePC, releaseRunning,
      _, _, _, releaseFrame⟩ :=
    SharedGraphReclaim.setup_execution program state start (start + 7) (withValues retained values) extra
      position running (by omega) heapStored extraFits releaseAt
  obtain ⟨pushed, pushTrace, pushHeap, pushStack, pushOutput, pushPC, pushRunning, pushFrame⟩ :=
    push_execution program ((List.finRange n).map (fun channel => boolWord width (fresh channel))) released
      (start + 7) releasePC releaseRunning (by simp only [List.length_map, List.length_finRange]; omega) pushAt
  obtain ⟨rewritten, rewriteTrace, rewriteHeap, rewriteStack, rewriteOutput, rewritePC, rewriteRunning, rewriteHead⟩ :=
    SharedChannelRewrite.execution program pushed retained #[] values fresh (List.finRange n) released.stack
      (start + 7 + 2 * n)
      (by simpa only [List.length_map, List.length_finRange] using pushPC) pushRunning
      (by simp only [List.length_finRange]; omega) capacity
      (by rw [pushHeap, releaseHeap, Array.append_empty])
      pushStack rewriteAt
  obtain ⟨final, jumpTrace, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    jump_execution program rewritten _ back
      (by simpa only [List.length_finRange] using rewritePC) rewriteRunning (by omega) jumpAt
  have releasedLive : released.liveWords + extra.length = state.liveWords := by
    simp only [State.liveWords, releaseHeap, releaseStack, releaseOutput, heapStored, Array.size_append,
      List.size_toArray]
    omega
  have pushedLive : pushed.liveWords = released.liveWords + n := by
    simp only [State.liveWords, pushHeap, pushStack, pushOutput, List.length_append, List.length_map,
      List.length_finRange]
    omega
  have rewrittenLive : rewritten.liveWords ≤ pushed.liveWords := rewriteTrace.final_storage_le
  have joined := releaseTrace.append (pushTrace.append (rewriteTrace.append jumpTrace))
  refine ⟨final, max state.liveWords (max (released.liveWords + n)
      (max pushed.liveWords rewritten.liveWords)), ?_, ?_, ?_, ?_, ?_, finalPC, finalRunning, ?_⟩
  · have total : 4 * extra.length + 4 + (2 * ((List.finRange n).map (fun channel => boolWord width (fresh channel))).length +
        (3 * (List.finRange n).length + 2)) = 4 * extra.length + 5 * n + 6 := by
      simp only [List.length_map, List.length_finRange]; omega
    rw [total] at joined
    simpa only [List.length_map, List.length_finRange] using joined
  · simp only [max_le_iff]
    omega
  · rw [finalHeap, rewriteHeap, SharedChannelRewrite.replace_all, Array.append_empty]
  · rw [finalStack, rewriteStack, releaseStack]
  · rw [finalOutput, rewriteOutput, pushOutput, releaseOutput]
  · rw [finalFrame 4 (by decide), rewriteHead, pushFrame 4 (by decide), releaseFrame 4 (by decide) (by decide) (by decide)]

open Controller.Cost.SharedDetectorPrepared in
theorem kept_split (packet heap : Array (Word width)) (graph : Controller.Decoder.DAG n) (tags : List (Word width))
    (root slotBound : Nat) (packetLength : packet.size = packetSize graph) (tagCount : tags.length = graph.roots.length)
    (below : packetSize graph ≤ slotBound)
    (kept : EnumerationScan.Kept slotBound (preparedHeap packet graph tags root) heap) :
    heap = packet ++ heap.extract packet.size heap.size := by
  have total := preparedHeap_size packet graph tags root packetLength tagCount
  have preparedBound : packetSize graph ≤ preparedSize graph := by
    rw [preparedSize_eq, coordinateBase]; omega
  apply Array.ext
  · simp only [Array.size_append, Array.size_extract]
    rw [kept.1, total]; omega
  · intro index left right
    by_cases inPacket : index < packet.size
    · rw [Array.getElem_append_left inPacket]
      have cell := kept.2 index (by omega)
      rw [preparedHeap_prefix packet graph tags root index inPacket, Array.getElem?_eq_getElem left,
        Array.getElem?_eq_getElem inPacket] at cell
      exact Option.some.inj cell
    · rw [Array.getElem_append_right (by omega)]
      simp only [Array.getElem_extract]
      congr 1
      omega

section Execution
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored Controller.Cost.ForestInputStored
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.SharedDetectorPrepared Controller.Cost.SharedDetectorAssembly

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- One re-entrant oracle call. -/
theorem execution (parameters : Parameters) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (retained entry back : Nat) (program : Program (EnumerationScan.Width parameters graph retained) 8)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (suffix : List (Word (EnumerationScan.Width parameters graph retained))) (state : State (EnumerationScan.Width parameters graph retained) 8)
    (position : state.pc = word (EnumerationScan.Width parameters graph retained) entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap (EnumerationScan.Width parameters graph retained) parameters.channels rows roots) rows roots
      (assignmentOfSet {parameters.bridge.target}))
    (input : state.stack = SharedRetainedCandidates.masks (EnumerationScan.Width parameters graph retained)
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F)) ++ suffix)
    (held : state.reg 4 = word (EnumerationScan.Width parameters graph retained) parameters.bridge.target.val)
    (room : entry + (code parameters graph T F (EnumerationScan.Width parameters graph retained) rows roots entry back).length + preparedSize graph ≤ retained)
    (present : SharedRootRead.BlockAt program entry (code parameters graph T F (EnumerationScan.Width parameters graph retained) rows roots entry back)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = false ∧ final.pc = word (EnumerationScan.Width parameters graph retained) back ∧
      final.reg 4 = word (EnumerationScan.Width parameters graph retained) (if answer then 1 else 0) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      ticks ≤ (parameters.channels + graph.roots.length + 1) * (5200 * (graph.countedSize + 1)) ∧
      peak ≤ state.liveWords + 210 * (graph.countedSize + 1) ∧
      (answer = true ↔ ∃ output : Fin graph.roots.length, SharedDetectorFeasibility.AtRoot parameters graph T F output) := by
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) < 2 ^ (EnumerationScan.Width parameters graph retained) at capacity
  have size := graph.countedSize_eq
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have preparedBound := preparedSize_le graph
  have preparedValue := preparedSize_eq graph
  have coordinateValue := coordinateBase_eq graph
  have coordinatePacket : coordinateBase graph = packetSize graph + 2 * graph.roots.length := rfl
  have packetValue : packetSize graph = rootBase graph + graph.roots.length + parameters.channels := rfl
  have maskValue : maskBase graph = rootBase graph + graph.roots.length := rfl
  have rootBaseValue : rootBase graph =
      5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences := rfl
  have slotValue : slot graph = coordinateBase graph + (parameters.channels + graph.nodeCount) := rfl
  have eC : candidatesEntry entry = entry + 8 := rfl
  have eD : directoryEntry parameters graph entry =
      entry + 8 + (10 * graph.roots.length + 14 * parameters.channels + 620) := rfl
  have eS : setupEntry parameters graph entry = directoryEntry parameters graph entry + (4 * graph.roots.length + 11) := rfl
  have eH : handoffEntry parameters graph entry =
      setupEntry parameters graph entry + 2 * (3 * (parameters.channels + graph.nodeCount) + 1) := rfl
  have eL : scanEntry parameters graph entry = handoffEntry parameters graph entry + 7 := rfl
  have scanEnd := scanCode_length parameters graph T F (EnumerationScan.Width parameters graph retained) entry
  have lengthEq := code_length parameters graph T F (EnumerationScan.Width parameters graph retained) rows roots entry back rootMatches
  rw [lengthEq] at room
  -- Code segments.
  unfold code at present
  have guardAt := block_left program entry _ _ present
  have afterGuard := block_right program entry _ _ present
  have candidatesAt : CodeAt program (candidatesEntry entry)
      (SharedRetainedCandidates.code (EnumerationScan.Width parameters graph retained) parameters.channels rows roots (candidatesEntry entry)
        (directoryEntry parameters graph entry)) :=
    block_code program _ _ (block_move program (block_left program _ _ _ afterGuard) (by simp [candidatesEntry]))
  have afterCandidates := block_right program _ _ _ afterGuard
  have directoryAt : SharedRootRead.BlockAt program (directoryEntry parameters graph entry)
      (SharedDetectorDirectoryAlloc.code (EnumerationScan.Width parameters graph retained) (packetSize graph) (rootBase graph) graph.roots.length
        (directoryEntry parameters graph entry)) :=
    block_move program (block_left program _ _ _ afterCandidates) (by simp [rootCount]; omega)
  have afterDirectory := block_right program _ _ _ afterCandidates
  have setupAt : SharedRootRead.BlockAt program (setupEntry parameters graph entry)
      (SharedCoordinateTable.code (EnumerationScan.Width parameters graph retained) (setupWords (EnumerationScan.Width parameters graph retained) graph (firstRoot parameters graph))) :=
    block_move program (block_left program _ _ _ afterDirectory) (by simp [rootCount]; omega)
  have afterSetup := block_right program _ _ _ afterDirectory
  have handoffAt : SharedRootRead.BlockAt program (handoffEntry parameters graph entry)
      (SharedDetectorSteps.handoffCode (EnumerationScan.Width parameters graph retained) (tableBase graph) (inverseBase graph) graph.roots.length (packetSize graph)) :=
    block_move program (block_left program _ _ _ afterSetup) (by simp [rootCount]; omega)
  have afterHandoff := block_right program _ _ _ afterSetup
  have scanAt : SharedRootRead.BlockAt program (scanEntry parameters graph entry)
      (scanCode parameters graph T F (EnumerationScan.Width parameters graph retained) entry) :=
    block_move program (block_left program _ _ _ afterHandoff) (by simp [rootCount]; omega)
  have teardownAt : SharedRootRead.BlockAt program (teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry)
      (teardownCode parameters graph T F (EnumerationScan.Width parameters graph retained) entry back) :=
    block_move program (block_right program _ _ _ afterHandoff) (by simp [rootCount]; omega)
  -- Output-count guard.
  have countCell : state.heap[4]? = some (word (EnumerationScan.Width parameters graph retained) graph.roots.length) := by
    rw [heapStored]; exact packet_outputs graph rows roots rootMatches _
  obtain ⟨guarded', guardTicks, guardTrace, guardTime, guardHeap, guardStack, guardOutput, guardRunning,
      emptyCase, nonemptyCase⟩ :=
    guard_execution program state entry back graph.roots.length position running (by omega) (by omega)
      countCell guardAt
  by_cases emptyOutputs : graph.roots.length = 0
  · obtain ⟨pc, decision⟩ := emptyCase emptyOutputs
    refine ⟨false, guarded', guardTicks, state.liveWords, guardTrace, guardRunning, pc, by simpa using decision,
      guardHeap, guardStack, guardOutput, ?_, by omega, ?_⟩
    · have := Nat.le_mul_of_pos_left (5200 * (graph.countedSize + 1))
        (by omega : 0 < parameters.channels + graph.roots.length + 1)
      omega
    · simp only [Bool.false_eq_true, false_iff, not_exists]
      intro output
      exact absurd output.isLt (by omega)
  obtain ⟨guardPC, guardFrame⟩ := nonemptyCase emptyOutputs
  have nonemptyRoots : graph.roots ≠ [] := fun empty => emptyOutputs (by simp [empty])
  obtain ⟨root, tail, rootsEq⟩ := List.exists_cons_of_ne_nil nonemptyRoots
  have head : graph.roots.head? = some root := by rw [rootsEq]; rfl
  have teardownValue : teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry =
      EnumerationLoop.returnPoint parameters graph T F (preparedSize graph) (coordinateBase graph) (slot graph)
        (scanEntry parameters graph entry) root (EnumerationScan.Width parameters graph retained) + 8 := by
    unfold teardownEntry; rw [head]
  have teardownBound := teardownEntry_bound parameters graph T F (EnumerationScan.Width parameters graph retained) entry
  -- Shared candidate evaluations.
  obtain ⟨candidated, candidateTicks, candidatePeak, candidateTrace, candidateTime, candidateSpace,
      candidateHeap, candidateStack, candidateOutput, candidatePC, candidateRunning, candidateHead⟩ :=
    SharedRetainedCandidates.execution program guarded' graph rows roots matched heads rootMatches
      parameters.bridge.target (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F))
      suffix (candidatesEntry entry) (directoryEntry parameters graph entry)
      (by omega) candidatesAt (by omega)
      (by simpa only [eC] using guardPC) guardRunning (guardHeap.trans heapStored) (guardStack.trans input) (by simp)
      ((guardFrame 4 (by decide)).trans held)
  have packetLength : candidated.heap.size = packetSize graph := by
    rw [candidateHeap]; exact packet_size graph rows roots matched rootMatches _
  have foldEq := tags_positions graph (extensionBase parameters.buses parameters.bridge.target T) F (EnumerationScan.Width parameters graph retained)
  have tagCount : ((List.finRange graph.roots.length).map
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (EnumerationScan.Width parameters graph retained))).length =
      graph.roots.length := by simp
  -- Candidate directory.
  obtain ⟨directed, directoryPeak, directoryTrace, directorySpace, directoryHeap, directoryStack, directoryOutput,
      directoryPC, directoryRunning⟩ :=
    SharedDetectorDirectoryAlloc.execution program candidated
      ((List.finRange graph.roots.length).map
        (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (EnumerationScan.Width parameters graph retained)))
      (rootWords (EnumerationScan.Width parameters graph retained) graph)
      (SharedHealthyReference.reference graph parameters.bridge.target (EnumerationScan.Width parameters graph retained) ++
        (SharedRetainedCandidates.masks (EnumerationScan.Width parameters graph retained) (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
          ((List.finRange parameters.channels).map (assignmentOfSet F)) ++ suffix))
      (rootBase graph) (directoryEntry parameters graph entry) (by simp) candidatePC candidateRunning
      (by rw [tagCount]; omega)
      (by rw [tagCount, packetLength]; omega)
      (by simp only [rootBase]; omega)
      (by rw [packetLength]; simp only [rootWords_length, packetSize, maskBase]; omega)
      (by rw [candidateHeap]; exact packet_roots graph rows roots matched rootMatches _)
      (by rw [candidateStack, foldEq]; simp only [List.append_assoc])
      (by rw [packetLength, tagCount]; exact directoryAt)
  -- Coordinate table, query slot and reserved tables.
  have rootValue := firstRoot_head parameters graph root head
  rw [rootValue] at setupAt
  obtain ⟨prepared, setupTrace, setupHeap, setupStack, setupOutput, setupPC, setupRunning, setupHead⟩ :=
    SharedCoordinateTable.execution program directed (setupWords (EnumerationScan.Width parameters graph retained) graph root.val) (setupEntry parameters graph entry)
      (by rw [directoryPC, tagCount, eS, Nat.add_assoc]) directoryRunning
      (by simp only [setupWords_length]; omega)
      (by rw [directoryHeap]; simp only [Array.size_append, List.size_toArray, rootWords_length, tagCount, packetLength,
          setupWords_length]; omega)
      setupAt
  have preparedEq : prepared.heap = preparedHeap candidated.heap graph
      ((List.finRange graph.roots.length).map
        (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (EnumerationScan.Width parameters graph retained))) root.val := by
    rw [setupHeap, directoryHeap]; rfl
  have preparedLength : prepared.heap.size = preparedSize graph := by
    rw [preparedEq]; exact preparedHeap_size _ graph _ root.val packetLength tagCount
  -- Register and stack handoff.
  obtain ⟨handed, handoffPeak, handoffTrace, handoffSpace, handedHeap, handedOutput, handedStack, handedPC,
      handedRunning, handedZero, handedTable, handedInverse⟩ :=
    SharedDetectorSteps.handoff_execution program prepared (handoffEntry parameters graph entry) (tableBase graph)
      (inverseBase graph) graph.roots.length (packetSize graph)
      (by rw [setupPC, setupWords_length, eH]) setupRunning (by omega) handoffAt
  have handedSize : handed.heap.size = preparedSize graph := by rw [handedHeap]; exact preparedLength
  -- Returning scan.
  have scanCodeEq : scanCode parameters graph T F (EnumerationScan.Width parameters graph retained) entry =
      EnumerationLoop.code parameters graph T F (Array.replicate (preparedSize graph) (word (EnumerationScan.Width parameters graph retained) 0))
        (layout graph _ (by simp)) (coordinateBase graph) (slot graph) graph.roots.length
        (scanEntry parameters graph entry) (teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry) root := by
    unfold scanCode; rw [head]
  have sameCode := EnumerationLoop.shared parameters graph T F
    (Array.replicate (preparedSize graph) (word (EnumerationScan.Width parameters graph retained) 0)) handed.heap
    (layout graph _ (by simp)) (layout graph handed.heap.size handedSize)
    (coordinateBase graph) (slot graph) graph.roots.length (scanEntry parameters graph entry)
    (teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry) root root (by simp [handedSize]) rfl rfl
  have scanPresent : SharedRootRead.BlockAt program (scanEntry parameters graph entry)
      (EnumerationLoop.code parameters graph T F handed.heap (layout graph handed.heap.size handedSize)
        (coordinateBase graph) (slot graph) graph.roots.length (scanEntry parameters graph entry)
        (teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry) root) := by
    rw [← sameCode, ← scanCodeEq]; exact scanAt
  have scanRoom : scanEntry parameters graph entry + (EnumerationLoop.code parameters graph T F handed.heap
      (layout graph handed.heap.size handedSize) (coordinateBase graph) (slot graph) graph.roots.length
      (scanEntry parameters graph entry) (teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry) root).length ≤ retained := by
    rw [← sameCode, ← scanCodeEq]; omega
  have ready := EnumerationPrepared.scan_ready parameters graph guarded T F retained (scanEntry parameters graph entry)
    (teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry)
    program (SharedRetainedCandidates.masks (EnumerationScan.Width parameters graph retained) (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F)) ++ suffix)
    candidated.heap root handed packetLength
    (by rw [candidateHeap]; exact packet_channels graph rows roots _)
    (by rw [candidateHeap]; exact packet_nodes graph rows roots matched _)
    (by intro channel; rw [candidateHeap]; exact packet_mask graph rows roots matched rootMatches _ channel)
    (by rw [handedHeap, preparedEq])
    handedSize
    (by rw [handedStack, setupStack, directoryStack])
    (by rw [handedPC, eL]) handedRunning handedZero handedTable handedInverse
    (by omega) scanRoom scanPresent
  obtain ⟨answer, scanned, scanTicks, scanPeak, scanTrace, scanRunning, scanPC, decision, scanStack, scanOutput,
      scanKept, scanTime, scanSpace, meaning⟩ :=
    EnumerationScan.execution parameters graph guarded T F consistent retained (coordinateBase graph)
      (slot graph) (slot graph + 1) graph.roots.length (maskBase graph) (scanEntry parameters graph entry)
      (teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry) program _ (List.finRange graph.roots.length) handed
      (packetSize graph) ready
  -- Teardown: release the prepared region.
  have scanHeap : scanned.heap = candidated.heap ++ scanned.heap.extract candidated.heap.size scanned.heap.size := by
    have kept : EnumerationScan.Kept (slot graph) (preparedHeap candidated.heap graph
        ((List.finRange graph.roots.length).map
          (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (EnumerationScan.Width parameters graph retained))) root.val)
        scanned.heap := by
      rw [← preparedEq, ← handedHeap]; exact scanKept
    exact kept_split candidated.heap scanned.heap graph _ root.val (slot graph) packetLength tagCount (by omega) kept
  have scannedSize : scanned.heap.size = preparedSize graph := by rw [scanKept.1, handedSize]
  have releaseCount : (scanned.heap.extract candidated.heap.size scanned.heap.size).toList.length =
      2 * graph.roots.length + 3 * (parameters.channels + graph.nodeCount) + 1 := by
    simp only [Array.length_toList, Array.size_extract, scannedSize, packetLength]; omega
  have cacheSize : (cacheHeap (EnumerationScan.Width parameters graph retained) (packetHeaderHeap (EnumerationScan.Width parameters graph retained) parameters.channels rows roots) rows roots).size =
      maskBase graph := by
    obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
    simp only [cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount, maskBase, rootBase]
  have teardownPresent : SharedRootRead.BlockAt program (teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry)
      ((SharedEvaluationReclaim.code (EnumerationScan.Width parameters graph retained) (teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry)
        (teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry + 7)
        (scanned.heap.extract candidated.heap.size scanned.heap.size).toList.length).toList ++
      (pushCode (EnumerationScan.Width parameters graph retained) ((List.finRange parameters.channels).map
        (fun channel => boolWord (EnumerationScan.Width parameters graph retained) (assignmentOfSet {parameters.bridge.target} channel))) ++
      (SharedChannelRewrite.code (EnumerationScan.Width parameters graph retained)
        (cacheHeap (EnumerationScan.Width parameters graph retained) (packetHeaderHeap (EnumerationScan.Width parameters graph retained) parameters.channels rows roots) rows roots).size
        (List.finRange parameters.channels) ++
      [.constant 0 (word (EnumerationScan.Width parameters graph retained) 0), .branchZero 0 (word (EnumerationScan.Width parameters graph retained) back)]))) := by
    have whole := teardownAt
    unfold teardownCode healthyWords at whole
    rw [releaseCount, cacheSize] <;> exact whole
  have scannedStored : scanned.heap = withValues
      (cacheHeap (EnumerationScan.Width parameters graph retained) (packetHeaderHeap (EnumerationScan.Width parameters graph retained) parameters.channels rows roots) rows roots)
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T)) ++
      (scanned.heap.extract candidated.heap.size scanned.heap.size).toList.toArray := by
    rw [Array.toArray_toList]
    have packetEq : candidated.heap = withValues
        (cacheHeap (EnumerationScan.Width parameters graph retained)
          (packetHeaderHeap (EnumerationScan.Width parameters graph retained) parameters.channels rows roots) rows roots)
        (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T)) := candidateHeap
    exact scanHeap.trans (congrArg
      (fun packet => packet ++ scanned.heap.extract candidated.heap.size scanned.heap.size) packetEq)
  obtain ⟨final, teardownPeak, teardownTrace, teardownSpace, finalHeap, finalStack, finalOutput, finalPC,
      finalRunning, finalHead⟩ :=
    teardown_execution program scanned (teardownEntry parameters graph T F (EnumerationScan.Width parameters graph retained) entry) back
      (cacheHeap (EnumerationScan.Width parameters graph retained) (packetHeaderHeap (EnumerationScan.Width parameters graph retained) parameters.channels rows roots) rows roots)
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      (assignmentOfSet {parameters.bridge.target})
      (scanned.heap.extract candidated.heap.size scanned.heap.size).toList scanPC scanRunning
      (by omega) (by rw [cacheSize]; omega) (by rw [releaseCount]; omega) scannedStored teardownPresent
  -- Composition and accounting.
  have finalDecision : final.reg 4 = word (EnumerationScan.Width parameters graph retained) (if answer then 1 else 0) := by
    rw [finalHead]; exact decision
  have restoredHeap : final.heap = state.heap := by
    rw [finalHeap, heapStored]; rfl
  have restoredStack : final.stack = state.stack := by
    rw [finalStack, scanStack, input]
  have restoredOutput : final.output = state.output := by
    rw [finalOutput, scanOutput, handedOutput, setupOutput, directoryOutput, candidateOutput, guardOutput]
  have packetState : state.heap.size = packetSize graph := by
    rw [heapStored]; exact packet_size graph rows roots matched rootMatches _
  have stackState : state.stack.length = 2 * parameters.channels + suffix.length := by
    rw [input]; simp; omega
  have foldLength : (SharedHeadLoop.witnessFold graph
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T)) 0
      ((List.finRange parameters.channels).map (assignmentOfSet F))
      (SharedBaselineInitialize.witnesses graph
        (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T)) (EnumerationScan.Width parameters graph retained))).length =
      graph.roots.length := by rw [foldEq]; simp
  have referenceLength : (SharedHealthyReference.reference graph parameters.bridge.target (EnumerationScan.Width parameters graph retained)).length =
      graph.roots.length := by simp [SharedHealthyReference.reference]
  have masksLength : (SharedRetainedCandidates.masks (EnumerationScan.Width parameters graph retained)
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F))).length = 2 * parameters.channels := by
    simp; omega
  have stateUnfold : state.liveWords = 8 + state.heap.size + state.stack.length + state.output.length + 1 := rfl
  have candidatedLive : candidated.liveWords = state.liveWords + 2 * graph.roots.length := by
    have stackLength : candidated.stack.length =
        graph.roots.length + graph.roots.length + (2 * parameters.channels + suffix.length) := by
      rw [candidateStack]; simp only [List.length_append, foldLength, referenceLength, masksLength]; omega
    have outputSame : candidated.output.length = state.output.length := by rw [candidateOutput, guardOutput]
    have unfold' : candidated.liveWords = 8 + candidated.heap.size + candidated.stack.length + candidated.output.length + 1 := rfl
    omega
  have directedLive : directed.liveWords = state.liveWords + 3 * graph.roots.length := by
    have heapSize : directed.heap.size = packetSize graph + 2 * graph.roots.length := by
      rw [directoryHeap]; simp only [Array.size_append, List.size_toArray, rootWords_length, tagCount, packetLength]
      omega
    have stackLength : directed.stack.length = graph.roots.length + (2 * parameters.channels + suffix.length) := by
      rw [directoryStack]; simp only [List.length_append, referenceLength, masksLength]
    have outputSame : directed.output.length = state.output.length := by
      rw [directoryOutput, candidateOutput, guardOutput]
    have unfold' : directed.liveWords = 8 + directed.heap.size + directed.stack.length + directed.output.length + 1 := rfl
    omega
  have preparedLive : prepared.liveWords = state.liveWords + 3 * graph.roots.length +
      (3 * (parameters.channels + graph.nodeCount) + 1) := by
    have heapSize : prepared.heap.size = directed.heap.size + (3 * (parameters.channels + graph.nodeCount) + 1) := by
      rw [setupHeap]; simp only [Array.size_append, List.size_toArray, setupWords_length]
    simp only [State.liveWords, heapSize, setupStack, setupOutput] at directedLive ⊢
    omega
  have handedLive : handed.liveWords = state.liveWords + 3 * graph.roots.length +
      (3 * (parameters.channels + graph.nodeCount) + 1) + 2 := by
    simp only [State.liveWords, handedHeap, handedStack, handedOutput, List.length_cons] at preparedLive ⊢
    omega
  have scannedLive : scanned.liveWords = state.liveWords +
      (2 * graph.roots.length + 3 * (parameters.channels + graph.nodeCount) + 1) := by
    have unfold' : scanned.liveWords = 8 + scanned.heap.size + scanned.stack.length + scanned.output.length + 1 := rfl
    have heapSize : scanned.heap.size = state.heap.size +
        (2 * graph.roots.length + 3 * (parameters.channels + graph.nodeCount) + 1) := by
      rw [scannedSize, packetState, preparedValue, coordinateValue]; omega
    have stackSame : scanned.stack.length = state.stack.length := by rw [scanStack, input]
    have outputSame : scanned.output.length = state.output.length := by
      rw [scanOutput, handedOutput, setupOutput, directoryOutput, candidateOutput, guardOutput]
    omega
  have guardedStack : guarded'.stack.length = 2 * parameters.channels + suffix.length := by
    rw [guardStack]; exact stackState
  have guardedOutput : guarded'.output.length = state.output.length := by rw [guardOutput]
  rw [guardedStack, guardedOutput] at candidateSpace
  rw [candidatedLive, tagCount] at directorySpace
  rw [preparedLive] at handoffSpace
  rw [handedLive] at scanSpace
  rw [scannedLive] at teardownSpace
  simp only [List.length_finRange] at scanTime
  have setupCount : (setupWords (EnumerationScan.Width parameters graph retained) graph root.val).length = 3 * (parameters.channels + graph.nodeCount) + 1 := by
    simp only [setupWords_length]
  have joined := guardTrace.append (candidateTrace.append (directoryTrace.append (setupTrace.append
    (handoffTrace.append (scanTrace.append teardownTrace)))))
  refine ⟨answer, final, _, _, joined, finalRunning, finalPC, finalDecision, restoredHeap, restoredStack, restoredOutput,
    ?_, ?_, ?_⟩
  · have channelRoom : parameters.channels * (84 * graph.countedSize + 54) + parameters.channels * 5 ≤
        parameters.channels * (5200 * (graph.countedSize + 1)) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    have outputRoom : graph.roots.length * (4900 * (graph.countedSize + 1)) + graph.roots.length * 18 ≤
        graph.roots.length * (5200 * (graph.countedSize + 1)) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega
  · have setupPeak : directed.liveWords + (setupWords (EnumerationScan.Width parameters graph retained) graph root.val).length ≤
        state.liveWords + 210 * (graph.countedSize + 1) := by
      rw [directedLive, setupCount]; omega
    simp only [max_le_iff]
    refine ⟨by omega, by simp only [State.liveWords] at stackState ⊢; omega, by omega, setupPeak, by omega,
      by omega, by omega⟩
  · rw [meaning]
    constructor
    · rintro ⟨output, _, feasible⟩; exact ⟨output, feasible⟩
    · rintro ⟨output, feasible⟩; exact ⟨output, List.mem_finRange output, feasible⟩

end Execution

end Controller.Cost.EnumerationOracle
