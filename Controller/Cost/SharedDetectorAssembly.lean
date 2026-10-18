module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedDetectorPrepared

@[expose] public section

/-! The complete shared detector and partial-extension decision on one loaded guarded graph.
One resident program checks the output count, runs the singleton reference, baseline and
head evaluations once, records one witness tag per output, prepares one reusable zero-query
heap, and then scans the outputs with one zero-system pass each. The decision is the final
value of register 4; an accepted run also emits a natively checked model. -/
namespace Controller.Cost.SharedDetectorAssembly
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops Controller.Cost.ForestZeroDictionary
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.SharedDetectorPrepared

theorem block_left (program : Program width 8) (entry : Nat) (first rest : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (first ++ rest)) : SharedRootRead.BlockAt program entry first := by
  intro offset below
  have found := present offset (by simp only [List.length_append]; omega)
  rwa [List.getElem?_append_left below] at found

theorem block_right (program : Program width 8) (entry : Nat) (first rest : List (Instruction width 8))
    (present : SharedRootRead.BlockAt program entry (first ++ rest)) :
    SharedRootRead.BlockAt program (entry + first.length) rest := by
  intro offset below
  have found := present (first.length + offset) (by simp only [List.length_append]; omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at found
  simpa only [Nat.add_assoc] using found

theorem block_move (program : Program width 8) {entry moved : Nat} {instructions : List (Instruction width 8)}
    (present : SharedRootRead.BlockAt program entry instructions) (same : entry = moved) :
    SharedRootRead.BlockAt program moved instructions := by
  subst same; exact present

theorem block_code (program : Program width 8) (entry : Nat) (instructions : Program width 8)
    (present : SharedRootRead.BlockAt program entry instructions.toList) : CodeAt program entry instructions := by
  intro phase
  simpa only [Array.getElem?_toList] using present phase.val (by simpa only [Array.length_toList] using phase.isLt)


/-- Shared graph evaluations performed by the candidate pass: the singleton reference, the
baseline when it is nonempty, and each head that is neither already true nor excluded
(`SharedHeadLoop.witnessStep` skips exactly the others). -/
def evaluations (baseline : Assignment n) (flags : List Bool) : Nat :=
  1 + (if (List.finRange n).any baseline then 1 else 0) +
    ((List.finRange n).zip flags).countP (fun pair => !baseline pair.1 && !pair.2)

theorem heads_sublist (baseline : Assignment n) : ∀ (channels : List (Fin n)) (flags : List Bool),
    (((channels.zip flags).filter (fun pair => !baseline pair.1 && !pair.2)).map Prod.fst).Sublist
      (channels.filter (fun channel => !baseline channel))
  | [], _ => by simp
  | _ :: _, [] => by simp
  | channel :: rest, flag :: others => by
    have tail := heads_sublist baseline rest others
    by_cases value : baseline channel
    · cases flag <;> simpa [List.filter_cons, value] using tail
    · cases flag
      · simpa [List.filter_cons, value] using tail.cons₂ channel
      · simpa [List.filter_cons, value] using tail.cons channel

theorem evaluations_le (baseline : Assignment n) (flags : List Bool) :
    evaluations baseline flags ≤ n + 1 := by
  unfold evaluations
  have heads : ((List.finRange n).zip flags).countP (fun pair => !baseline pair.1 && !pair.2) ≤
      ((List.finRange n).filter (fun channel => !baseline channel)).length := by
    rw [List.countP_eq_length_filter]
    simpa using (heads_sublist baseline (List.finRange n) flags).length_le
  cases nonempty : (List.finRange n).any baseline with
  | false =>
    have := List.length_filter_le (fun channel => !baseline channel) (List.finRange n)
    simp only [List.length_finRange] at this
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  | true =>
    obtain ⟨channel, member, value⟩ := List.any_eq_true.mp nonempty
    have strict : ((List.finRange n).filter (fun channel => !baseline channel)).length < n := by
      have lt := (List.length_filter_lt_length_iff_exists (p := fun channel => !baseline channel)
        (l := List.finRange n)).mpr ⟨channel, member, by simp [value]⟩
      simpa using lt
    simp only [↓reduceIte]
    omega

section Code
variable (parameters : Parameters) (graph : DAG parameters.channels) (T F : Finset (Fin parameters.channels))

def candidatesEntry (entry : Nat) : Nat := entry + 7

def directoryEntry (entry : Nat) : Nat :=
  candidatesEntry entry + (10 * graph.roots.length + 14 * parameters.channels + 620)

def setupEntry (entry : Nat) : Nat := directoryEntry parameters graph entry + (4 * graph.roots.length + 11)

def handoffEntry (entry : Nat) : Nat :=
  setupEntry parameters graph entry + 2 * (3 * (parameters.channels + graph.nodeCount) + 1)

def loopEntry (entry : Nat) : Nat := handoffEntry parameters graph entry + 7

/-- The first declared root names the shared query slot before the first query retargets it. -/
def firstRoot : Nat := match graph.roots.head? with
  | none => 0
  | some root => root.val

/-- The loop instructions depend on the prepared heap only through its size and table bases. -/
def loopCode (width entry : Nat) : List (Instruction width 8) :=
  match graph.roots.head? with
  | none => []
  | some root => SharedRootDetectorResident.code parameters graph T F
      (Array.replicate (preparedSize graph) (word width 0))
      (layout graph _ (by simp)) (coordinateBase graph) (slot graph) graph.roots.length (maskBase graph)
      (loopEntry parameters graph entry) root

def code (width : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) : List (Instruction width 8) :=
  SharedDetectorSteps.guardCode width entry ++
    ((SharedRetainedCandidates.code width parameters.channels rows roots (candidatesEntry entry)
      (directoryEntry parameters graph entry)).toList ++
    (SharedDetectorDirectoryAlloc.code width (packetSize graph) (rootBase graph) graph.roots.length
      (directoryEntry parameters graph entry) ++
    (SharedCoordinateTable.code width (setupWords width graph (firstRoot parameters graph)) ++
    (SharedDetectorSteps.handoffCode width (tableBase graph) (inverseBase graph) graph.roots.length (packetSize graph) ++
      loopCode parameters graph T F width entry))))

theorem loopCode_length_bound (width entry : Nat) :
    (loopCode parameters graph T F width entry).length ≤
      410 * (graph.countedSize + 1) + 77 * (selectedSize parameters).total + 563 := by
  unfold loopCode
  split
  · simp
  · exact SharedRootDetectorResident.code_length_bound parameters graph T F _ _ _ _ _ _ _ _

theorem code_length (width : Nat) (rows : List Row) (roots : List Nat) (entry : Nat)
    (rootMatches : RootsMatch graph roots) :
    (code parameters graph T F width rows roots entry).length =
      loopEntry parameters graph entry - entry + (loopCode parameters graph T F width entry).length := by
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  simp only [code, List.length_append, Array.length_toList, SharedRetainedCandidates.code_size, rootCount,
    SharedDetectorDirectoryAlloc.code_length, SharedCoordinateTable.code_length, setupWords_length,
    SharedDetectorSteps.guardCode_length, SharedDetectorSteps.handoffCode_length,
    loopEntry, handoffEntry, setupEntry, directoryEntry, candidatesEntry]
  omega

theorem code_length_bound (width : Nat) (rows : List Row) (roots : List Nat) (entry : Nat)
    (rootMatches : RootsMatch graph roots) :
    (code parameters graph T F width rows roots entry).length ≤
      450 * (graph.countedSize + 1) + 77 * (selectedSize parameters).total + 1300 := by
  rw [code_length parameters graph T F width rows roots entry rootMatches]
  have loop := loopCode_length_bound parameters graph T F width entry
  have size := graph.countedSize_eq
  simp only [loopEntry, handoffEntry, setupEntry, directoryEntry, candidatesEntry]
  omega

theorem loopCode_head (width entry : Nat) (root : Fin graph.nodeCount)
    (head : graph.roots.head? = some root) :
    loopCode parameters graph T F width entry = SharedRootDetectorResident.code parameters graph T F
      (Array.replicate (preparedSize graph) (word width 0))
      (layout graph _ (by simp)) (coordinateBase graph) (slot graph) graph.roots.length (maskBase graph)
      (loopEntry parameters graph entry) root := by
  unfold loopCode
  rw [head]

theorem firstRoot_head (root : Fin graph.nodeCount) (head : graph.roots.head? = some root) :
    firstRoot parameters graph = root.val := by
  unfold firstRoot
  rw [head]

end Code

/-- Retained-word capacity sufficient for the complete program at entry zero and the prepared heap. -/
def standaloneRetained (parameters : Parameters) (graph : DAG parameters.channels) : Nat :=
  460 * (graph.countedSize + 1) + 77 * (selectedSize parameters).total + 1300

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- One fetched run decides whether some output can be made to differ from its healthy
singleton value `{t}` by an admissible set extending the fixed channels `(T, F)`. The time
is `O((n+q)G)` plus `55N` for the accepted native lift; working words are `O(G)` plus `3N`. -/
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw) (drive : parameters.drive = true)
    (graph : DAG parameters.channels) (guarded : graph.Guarded) (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (retained entry : Nat) (program : Program (SharedDetectorLoop.Width parameters graph retained) 8)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots)
    (observations : Fin graph.roots.length → Fin parameters.decoder.roots.length)
    (observationEq : ∀ position K, parameters.observations (observations position) (assignmentOfSet K) =
      graph.eval (assignmentOfSet K) graph.roots[position.val])
    (suffix : List (Word (SharedDetectorLoop.Width parameters graph retained)))
    (state : State (SharedDetectorLoop.Width parameters graph retained) 8)
    (position : state.pc = word (SharedDetectorLoop.Width parameters graph retained) entry)
    (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap (SharedDetectorLoop.Width parameters graph retained)
      parameters.channels rows roots) rows roots (assignmentOfSet {parameters.bridge.target}))
    (input : state.stack = SharedRetainedCandidates.masks (SharedDetectorLoop.Width parameters graph retained)
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F)) ++ suffix)
    (held : state.reg 4 = word (SharedDetectorLoop.Width parameters graph retained) parameters.bridge.target.val)
    (room : entry + (code parameters graph T F (SharedDetectorLoop.Width parameters graph retained) rows roots entry).length +
      preparedSize graph ≤ retained)
    (present : SharedRootRead.BlockAt program entry
      (code parameters graph T F (SharedDetectorLoop.Width parameters graph retained) rows roots entry)) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution program state final ticks peak ∧ final.halted = true ∧
      final.reg 4 = word (SharedDetectorLoop.Width parameters graph retained) (if answer then 1 else 0) ∧
      ticks ≤ parameters.channels * (84 * graph.countedSize + 54) +
        graph.roots.length * (5032 * (graph.countedSize + 1)) +
        (216 * graph.countedSize + 10 * graph.roots.length + 6 * (parameters.channels + graph.nodeCount) + 115) +
        (if answer then 55 * (selectedSize parameters).total else 0) ∧
      peak ≤ state.liveWords + 210 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      (answer = true ↔ ∃ output : Fin graph.roots.length, SharedDetectorFeasibility.AtRoot parameters graph T F output) ∧
      (answer = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) := by
  have capacity := SharedMachineCapacity.capacity retained graph.countedSize (selectedSize parameters).total
  change 131072 * (retained + graph.countedSize + (selectedSize parameters).total + 1) < 2 ^ (SharedDetectorLoop.Width parameters graph retained) at capacity
  have size := graph.countedSize_eq
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have preparedBound := preparedSize_le graph
  have preparedValue := preparedSize_eq graph
  have coordinateValue := coordinateBase_eq graph
  have coordinatePacket : coordinateBase graph = packetSize graph + 2 * graph.roots.length := rfl
  have packetValue : packetSize graph = rootBase graph + graph.roots.length + parameters.channels := rfl
  have rootBaseValue : rootBase graph =
      5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences := rfl
  have eC : candidatesEntry entry = entry + 7 := rfl
  have eD : directoryEntry parameters graph entry =
      entry + 7 + (10 * graph.roots.length + 14 * parameters.channels + 620) := rfl
  have eS : setupEntry parameters graph entry = directoryEntry parameters graph entry + (4 * graph.roots.length + 11) := rfl
  have eH : handoffEntry parameters graph entry =
      setupEntry parameters graph entry + 2 * (3 * (parameters.channels + graph.nodeCount) + 1) := rfl
  have eL : loopEntry parameters graph entry = handoffEntry parameters graph entry + 7 := rfl
  have lengthEq := code_length parameters graph T F (SharedDetectorLoop.Width parameters graph retained) rows roots entry rootMatches
  rw [lengthEq] at room
  -- Code segments.
  unfold code at present
  have guardAt := block_left program entry _ _ present
  have afterGuard := block_right program entry _ _ present
  have candidatesAt : CodeAt program (candidatesEntry entry)
      (SharedRetainedCandidates.code (SharedDetectorLoop.Width parameters graph retained) parameters.channels rows roots (candidatesEntry entry)
        (directoryEntry parameters graph entry)) :=
    block_code program _ _ (block_move program (block_left program _ _ _ afterGuard) (by simp; omega))
  have afterCandidates := block_right program _ _ _ afterGuard
  have directoryAt : SharedRootRead.BlockAt program (directoryEntry parameters graph entry)
      (SharedDetectorDirectoryAlloc.code (SharedDetectorLoop.Width parameters graph retained) (packetSize graph) (rootBase graph) graph.roots.length
        (directoryEntry parameters graph entry)) :=
    block_move program (block_left program _ _ _ afterCandidates) (by simp [rootCount]; omega)
  have afterDirectory := block_right program _ _ _ afterCandidates
  have setupAt : SharedRootRead.BlockAt program (setupEntry parameters graph entry)
      (SharedCoordinateTable.code (SharedDetectorLoop.Width parameters graph retained) (setupWords (SharedDetectorLoop.Width parameters graph retained) graph (firstRoot parameters graph))) :=
    block_move program (block_left program _ _ _ afterDirectory) (by simp [rootCount]; omega)
  have afterSetup := block_right program _ _ _ afterDirectory
  have handoffAt : SharedRootRead.BlockAt program (handoffEntry parameters graph entry)
      (SharedDetectorSteps.handoffCode (SharedDetectorLoop.Width parameters graph retained) (tableBase graph) (inverseBase graph) graph.roots.length (packetSize graph)) :=
    block_move program (block_left program _ _ _ afterSetup) (by simp [rootCount]; omega)
  have loopAt : SharedRootRead.BlockAt program (loopEntry parameters graph entry)
      (loopCode parameters graph T F (SharedDetectorLoop.Width parameters graph retained) entry) :=
    block_move program (block_right program _ _ _ afterSetup) (by simp [rootCount]; omega)
  -- Output-count guard.
  have countCell : state.heap[4]? = some (word (SharedDetectorLoop.Width parameters graph retained) graph.roots.length) := by
    rw [heapStored]; exact packet_outputs graph rows roots rootMatches _
  obtain ⟨guarded', guardTrace, guardHeap, guardStack, guardOutput, emptyCase, nonemptyCase⟩ :=
    SharedDetectorSteps.guard_execution program state entry graph.roots.length position running (by omega) (by omega)
      countCell guardAt
  by_cases emptyOutputs : graph.roots.length = 0
  · obtain ⟨halted, decision⟩ := emptyCase emptyOutputs
    refine ⟨false, guarded', 5, state.liveWords, guardTrace, halted, by simpa using decision, ?_, ?_, ?_, ?_⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega
    · omega
    · simp only [Bool.false_eq_true, false_iff, not_exists]
      intro output
      exact absurd output.isLt (by omega)
    · intro impossible; cases impossible
  obtain ⟨guardRunning, guardPC, guardFrame⟩ := nonemptyCase emptyOutputs
  have nonemptyRoots : graph.roots ≠ [] := fun empty => emptyOutputs (by simp [empty])
  obtain ⟨root, tail, rootsEq⟩ := List.exists_cons_of_ne_nil nonemptyRoots
  have head : graph.roots.head? = some root := by rw [rootsEq]; rfl
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
  have foldEq := tags_positions graph (extensionBase parameters.buses parameters.bridge.target T) F (SharedDetectorLoop.Width parameters graph retained)
  have tagCount : ((List.finRange graph.roots.length).map
      (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (SharedDetectorLoop.Width parameters graph retained))).length =
      graph.roots.length := by simp
  -- Candidate directory.
  obtain ⟨directed, directoryPeak, directoryTrace, directorySpace, directoryHeap, directoryStack, directoryOutput,
      directoryPC, directoryRunning⟩ :=
    SharedDetectorDirectoryAlloc.execution program candidated
      ((List.finRange graph.roots.length).map
        (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (SharedDetectorLoop.Width parameters graph retained)))
      (rootWords (SharedDetectorLoop.Width parameters graph retained) graph)
      (SharedHealthyReference.reference graph parameters.bridge.target (SharedDetectorLoop.Width parameters graph retained) ++
        (SharedRetainedCandidates.masks (SharedDetectorLoop.Width parameters graph retained) (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
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
    SharedCoordinateTable.execution program directed (setupWords (SharedDetectorLoop.Width parameters graph retained) graph root.val) (setupEntry parameters graph entry)
      (by rw [directoryPC, tagCount, eS, Nat.add_assoc]) directoryRunning
      (by simp only [setupWords_length]; omega)
      (by rw [directoryHeap]; simp only [Array.size_append, List.size_toArray, rootWords_length, tagCount, packetLength,
          setupWords_length]; omega)
      setupAt
  have preparedEq : prepared.heap = preparedHeap candidated.heap graph
      ((List.finRange graph.roots.length).map
        (SharedWitnessDecode.tag graph (extensionBase parameters.buses parameters.bridge.target T) F (SharedDetectorLoop.Width parameters graph retained))) root.val := by
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
  -- Loop entry invariant.
  have sameCode := SharedRootDetectorResident.shared parameters graph T F
    (Array.replicate (preparedSize graph) (word (SharedDetectorLoop.Width parameters graph retained) 0)) handed.heap
    (layout graph _ (by simp)) (layout graph handed.heap.size handedSize)
    (coordinateBase graph) (slot graph) graph.roots.length (maskBase graph) (loopEntry parameters graph entry) root root
    (by simp [handedSize]) rfl rfl
  have loopCodeEq := loopCode_head parameters graph T F (SharedDetectorLoop.Width parameters graph retained) entry root head
  have loopPresent : SharedRootRead.BlockAt program (loopEntry parameters graph entry)
      (SharedRootDetectorResident.code parameters graph T F handed.heap (layout graph handed.heap.size handedSize)
        (coordinateBase graph) (slot graph) graph.roots.length (maskBase graph) (loopEntry parameters graph entry)
        root) := by
    rw [← sameCode, ← loopCodeEq]; exact loopAt
  have loopRoom : loopEntry parameters graph entry + (SharedRootDetectorResident.code parameters graph T F handed.heap
      (layout graph handed.heap.size handedSize) (coordinateBase graph) (slot graph) graph.roots.length (maskBase graph)
      (loopEntry parameters graph entry) root).length ≤ retained := by
    rw [← sameCode, ← loopCodeEq]; omega
  have ready := SharedDetectorPrepared.ready parameters graph guarded T F retained (loopEntry parameters graph entry)
    program (SharedRetainedCandidates.masks (SharedDetectorLoop.Width parameters graph retained) (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F)) ++ suffix)
    candidated.heap root handed packetLength
    (by rw [candidateHeap]; exact packet_channels graph rows roots _)
    (by rw [candidateHeap]; exact packet_nodes graph rows roots matched _)
    (by intro channel; rw [candidateHeap]; exact packet_mask graph rows roots matched rootMatches _ channel)
    (by rw [handedHeap, preparedEq])
    handedSize
    (by rw [handedStack, setupStack, directoryStack])
    (by rw [handedPC, eL]) handedRunning handedZero handedTable handedInverse
    (by omega) loopRoom loopPresent
  -- Output scan.
  obtain ⟨answer, final, loopTicks, loopPeak, loopTrace, halted, loopTime, loopSpace, meaning, checked, decision⟩ :=
    SharedDetectorLoop.execution parameters raw drive graph guarded T F consistent retained (coordinateBase graph)
      (slot graph) (slot graph + 1) graph.roots.length (maskBase graph) (loopEntry parameters graph entry) program
      _ observations observationEq (List.finRange graph.roots.length) handed (packetSize graph) ready
  -- Composition and accounting.
  have packetState : state.heap.size = packetSize graph := by
    rw [heapStored]; exact packet_size graph rows roots matched rootMatches _
  have stackState : state.stack.length = 2 * parameters.channels + suffix.length := by
    rw [input]; simp; omega
  have guardedLive : guarded'.liveWords = state.liveWords := by
    simp only [State.liveWords, guardHeap, guardStack, guardOutput]
  have foldLength : (SharedHeadLoop.witnessFold graph
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T)) 0
      ((List.finRange parameters.channels).map (assignmentOfSet F))
      (SharedBaselineInitialize.witnesses graph
        (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T)) (SharedDetectorLoop.Width parameters graph retained))).length =
      graph.roots.length := by rw [foldEq]; simp
  have referenceLength : (SharedHealthyReference.reference graph parameters.bridge.target (SharedDetectorLoop.Width parameters graph retained)).length =
      graph.roots.length := by simp [SharedHealthyReference.reference]
  have masksLength : (SharedRetainedCandidates.masks (SharedDetectorLoop.Width parameters graph retained)
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F))).length = 2 * parameters.channels := by
    simp; omega
  have stateLive : state.liveWords = 8 + packetSize graph + (2 * parameters.channels + suffix.length) +
      state.output.length + 1 := by
    simp only [State.liveWords, packetState, stackState]
  have candidatedLive : candidated.liveWords = state.liveWords + 2 * graph.roots.length := by
    have stackLength : candidated.stack.length =
        graph.roots.length + graph.roots.length + (2 * parameters.channels + suffix.length) := by
      rw [candidateStack]; simp only [List.length_append, foldLength, referenceLength, masksLength]; omega
    have outputSame : candidated.output = state.output := by rw [candidateOutput, guardOutput]
    simp only [State.liveWords, stackLength, outputSame, packetLength] at stateLive ⊢
    omega
  have directedLive : directed.liveWords = state.liveWords + 3 * graph.roots.length := by
    have heapSize : directed.heap.size = packetSize graph + 2 * graph.roots.length := by
      rw [directoryHeap]; simp only [Array.size_append, List.size_toArray, rootWords_length, tagCount, packetLength]
      omega
    have stackLength : directed.stack.length = graph.roots.length + (2 * parameters.channels + suffix.length) := by
      rw [directoryStack]; simp only [List.length_append, referenceLength, masksLength]
    have outputSame : directed.output.length = state.output.length := by
      rw [directoryOutput, candidateOutput, guardOutput]
    have directedUnfold : directed.liveWords =
        8 + directed.heap.size + directed.stack.length + directed.output.length + 1 := rfl
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
  have loopTime' : loopTicks ≤ graph.roots.length * (5032 * (graph.countedSize + 1)) +
      (if answer then 55 * (selectedSize parameters).total else 0) + 5 := by
    simpa only [List.length_finRange] using loopTime
  have trace := guardTrace.append (candidateTrace.append (directoryTrace.append
    (setupTrace.append (handoffTrace.append loopTrace))))
  rw [tagCount, setupWords_length] at trace
  refine ⟨answer, final, _, _, trace, halted, decision, ?_, ?_, ?_, checked⟩
  · cases answer <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at loopTime' ⊢ <;> omega
  · rw [candidatedLive, tagCount] at directorySpace
    rw [preparedLive] at handoffSpace
    rw [handedLive] at loopSpace
    have guardedStack : guarded'.stack.length = 2 * parameters.channels + suffix.length := by
      rw [guardStack]; exact stackState
    have guardedOutput : guarded'.output.length = state.output.length := by rw [guardOutput]
    rw [guardedStack, guardedOutput] at candidateSpace
    simp only [max_le_iff]
    refine ⟨by omega, by omega, by omega, by rw [directedLive]; omega, by omega, by omega⟩
  · rw [meaning]
    constructor
    · rintro ⟨output, _, feasible⟩; exact ⟨output, feasible⟩
    · rintro ⟨output, feasible⟩; exact ⟨output, List.mem_finRange output, feasible⟩

/-- The resident program at entry zero for the standalone capacity. -/
def program (parameters : Parameters) (graph : DAG parameters.channels) (T F : Finset (Fin parameters.channels))
    (rows : List Row) (roots : List Nat) :
    Program (SharedDetectorLoop.Width parameters graph (standaloneRetained parameters graph)) 8 :=
  (code parameters graph T F (SharedDetectorLoop.Width parameters graph (standaloneRetained parameters graph))
    rows roots 0).toArray

theorem program_words (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (rows : List Row) (roots : List Nat)
    (rootMatches : RootsMatch graph roots) :
    programWords (program parameters graph T F rows roots) ≤
      1800 * (graph.countedSize + 1) + 308 * (selectedSize parameters).total + 5200 := by
  have bound := code_length_bound parameters graph T F
    (SharedDetectorLoop.Width parameters graph (standaloneRetained parameters graph)) rows roots 0 rootMatches
  simp only [programWords, program, List.size_toArray]
  omega

set_option maxHeartbeats 4000000 in
/-- Capacity-free standalone form: no word-width, heap-room or code-placement premises remain. -/
theorem standalone_execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (drive : parameters.drive = true) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots)
    (observations : Fin graph.roots.length → Fin parameters.decoder.roots.length)
    (observationEq : ∀ position K, parameters.observations (observations position) (assignmentOfSet K) =
      graph.eval (assignmentOfSet K) graph.roots[position.val])
    (suffix : List (Word (SharedDetectorLoop.Width parameters graph (standaloneRetained parameters graph))))
    (state : State (SharedDetectorLoop.Width parameters graph (standaloneRetained parameters graph)) 8)
    (position : state.pc = word _ 0) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap
      (SharedDetectorLoop.Width parameters graph (standaloneRetained parameters graph))
      parameters.channels rows roots) rows roots (assignmentOfSet {parameters.bridge.target}))
    (input : state.stack = SharedRetainedCandidates.masks
      (SharedDetectorLoop.Width parameters graph (standaloneRetained parameters graph))
      (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
      ((List.finRange parameters.channels).map (assignmentOfSet F)) ++ suffix)
    (held : state.reg 4 = word _ parameters.bridge.target.val) :
    ∃ answer : Bool, ∃ final ticks peak,
      Execution (program parameters graph T F rows roots) state final ticks peak ∧ final.halted = true ∧
      final.reg 4 = word _ (if answer then 1 else 0) ∧
      ticks ≤ (parameters.channels + graph.roots.length + 1) * (5100 * (graph.countedSize + 1)) +
        (if answer then 55 * (selectedSize parameters).total else 0) ∧
      peak ≤ state.liveWords + 210 * (graph.countedSize + 1) + 3 * (selectedSize parameters).total ∧
      (answer = true ↔ ∃ output : Fin graph.roots.length, ∃ K, Admissible parameters.buses parameters.bridge.target K ∧
        ExtendsFixed T F K ∧ graph.eval (assignmentOfSet {parameters.bridge.target}) graph.roots[output.val] ≠
          graph.eval (assignmentOfSet K) graph.roots[output.val]) ∧
      (answer = true → Certificate.ModelCheck.check (formula parameters)
        (NativeRealizedChecked.decodeOutput final.output (compile parameters).toState.count) = true) := by
  have bound := code_length_bound parameters graph T F
    (SharedDetectorLoop.Width parameters graph (standaloneRetained parameters graph)) rows roots 0 rootMatches
  have prepared := preparedSize_le graph
  have retainedValue : standaloneRetained parameters graph =
      460 * (graph.countedSize + 1) + 77 * (selectedSize parameters).total + 1300 := rfl
  obtain ⟨answer, final, ticks, peak, trace, halted, decision, time, space, meaning, checked⟩ :=
    execution parameters raw drive graph guarded T F consistent (standaloneRetained parameters graph) 0
      (program parameters graph T F rows roots) rows roots matched heads rootMatches observations observationEq
      suffix state position running heapStored input held
      (by omega)
      (by intro offset _; simp [program])
  refine ⟨answer, final, ticks, peak, trace, halted, decision, ?_, space, meaning, checked⟩
  have size := graph.countedSize_eq
  have channelPart : parameters.channels * (84 * graph.countedSize + 54) ≤
      parameters.channels * (5100 * (graph.countedSize + 1)) := Nat.mul_le_mul_left _ (by omega)
  have outputSplit : graph.roots.length * (5100 * (graph.countedSize + 1)) =
      graph.roots.length * (5032 * (graph.countedSize + 1)) + graph.roots.length * (68 * (graph.countedSize + 1)) := by
    rw [← Nat.mul_add]; congr 1; omega
  have outputLinear : graph.roots.length * 10 ≤ graph.roots.length * (68 * (graph.countedSize + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

end Controller.Cost.SharedDetectorAssembly
