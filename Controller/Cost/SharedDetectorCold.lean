module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedDetectorAssembly

@[expose] public section

/-! Cold entry for the shared detector, with the input convention of the accepted forest
decision: an empty heap and the supplied packet words, the healthy singleton channel words,
the target identifier, the baseline mask and the exclusion flags on the stack. The packet is
moved onto the heap once by fetched pop/allocate pairs; no evaluation precedes the candidate
pass. -/
namespace Controller.Cost.SharedDetectorCold
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops
open Controller.Native Controller.Native.SourceController Controller.Cost.NativeSourceExecution
open Controller.Cost.SharedDetectorPrepared Controller.Cost.SharedDetectorAssembly

/-- Supplied packet followed by the healthy channel values. -/
def inputWords (width : Nat) (rows : List Row) (roots : List Nat) (values : Assignment n) : List (Word width) :=
  (inputPacket n 0 rows roots).map (word width) ++ List.ofFn (fun channel => boolWord width (values channel))

theorem inputWords_heap (width : Nat) (rows : List Row) (roots : List Nat) (values : Assignment n) :
    (#[] : Array (Word width)) ++ (inputWords width rows roots values).toArray =
      channelHeap (packetHeaderHeap width n rows roots) rows roots values := by
  simp only [Array.empty_append, inputWords, channelHeap, ForestInputStored.withValues, ← List.append_toArray,
    input_packet_cache]

theorem inputWords_length (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (rootMatches : RootsMatch graph roots) (values : Assignment n) :
    (inputWords width rows roots values).length = packetSize graph := by
  have size := congrArg Array.size (inputWords_heap width rows roots values)
  rw [packet_size graph rows roots matched rootMatches values] at size
  simpa using size

theorem pop_execution (program : Program width 8) (state : State width 8) (entry : Nat) (destination : Fin 8)
    (value : Word width) (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 1 < 2 ^ width) (present : program[entry]? = some (.pop destination))
    (input : state.stack = value :: rest) :
    ∃ final, Execution program state final 1 state.liveWords ∧
      final.pc = word width (entry + 1) ∧ final.reg destination = value ∧ final.heap = state.heap ∧
      final.stack = rest ∧ final.output = state.output ∧ final.halted = false ∧
      (∀ index : Fin 8, index ≠ destination → final.reg index = state.reg index) := by
  let final : State width 8 := { state.advance.put destination value with stack := rest }
  have stepped : step (.pop destination) state = some final := by simp [step, running, input, final]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  have live : final.liveWords ≤ state.liveWords := by
    simp only [final, State.liveWords, State.put, State.advance, input, List.length_cons]; omega
  refine ⟨final, ?_, ?_, by simp [final, State.put], rfl, rfl, rfl, running, ?_⟩
  · simpa only [Nat.max_eq_left live] using trace
  · simpa [final, State.put] using advance_position state position (by omega)
  · intro index other
    simp [final, State.put, State.advance, other]

section Code
variable (parameters : Parameters) (graph : DAG parameters.channels) (T F : Finset (Fin parameters.channels))

def detectorEntry : Nat := 2 * packetSize graph + 1

def code (width : Nat) (rows : List Row) (roots : List Nat) : List (Instruction width 8) :=
  SharedWitnessPark.code width (packetSize graph) ++ [.pop 4] ++
    SharedDetectorAssembly.code parameters graph T F width rows roots (detectorEntry parameters graph)

/-- Retained-word capacity for the cold program at entry zero and the prepared heap. -/
def retained : Nat := 480 * (graph.countedSize + 1) + 77 * (selectedSize parameters).total + 1300

def program (rows : List Row) (roots : List Nat) :
    Program (SharedDetectorLoop.Width parameters graph (retained parameters graph)) 8 :=
  (code parameters graph T F (SharedDetectorLoop.Width parameters graph (retained parameters graph)) rows roots).toArray

theorem code_length_bound (width : Nat) (rows : List Row) (roots : List Nat) (rootMatches : RootsMatch graph roots) :
    (code parameters graph T F width rows roots).length ≤
      470 * (graph.countedSize + 1) + 77 * (selectedSize parameters).total + 1300 := by
  have inner := SharedDetectorAssembly.code_length_bound parameters graph T F width rows roots
    (detectorEntry parameters graph) rootMatches
  have size := graph.countedSize_eq
  simp only [code, List.length_append, SharedWitnessPark.code_length, List.length_singleton]
  simp only [packetSize, maskBase, rootBase]
  omega

theorem program_words (rows : List Row) (roots : List Nat) (rootMatches : RootsMatch graph roots) :
    programWords (program parameters graph T F rows roots) ≤
      1880 * (graph.countedSize + 1) + 308 * (selectedSize parameters).total + 5200 := by
  have bound := code_length_bound parameters graph T F
    (SharedDetectorLoop.Width parameters graph (retained parameters graph)) rows roots rootMatches
  simp only [programWords, program, List.size_toArray]
  omega

end Code

set_option maxHeartbeats 4000000 in
/-- Capacity-free cold decision. From an empty heap and the supplied words, one fetched run
halts with register 4 equal to 1 exactly when some output differs from its value on the
healthy singleton `{t}` under an admissible set extending the fixed channels `(T, F)`; an
accepted run also emits a natively checked model. The time is `O((n+q)G)` plus `55N` only
for the accepted native lift; working words are `O(G)` plus `3N`. -/
theorem execution (parameters : Parameters) (raw : parameters.layout = .raw)
    (drive : parameters.drive = true) (graph : DAG parameters.channels) (guarded : graph.Guarded)
    (T F : Finset (Fin parameters.channels))
    (consistent : FixedConsistent (extensionBase parameters.buses parameters.bridge.target T) F)
    (rows : List Row) (roots : List Nat) (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots)
    (observations : Fin graph.roots.length → Fin parameters.decoder.roots.length)
    (observationEq : ∀ position K, parameters.observations (observations position) (assignmentOfSet K) =
      graph.eval (assignmentOfSet K) graph.roots[position.val])
    (suffix : List (Word (SharedDetectorLoop.Width parameters graph (retained parameters graph))))
    (state : State (SharedDetectorLoop.Width parameters graph (retained parameters graph)) 8)
    (position : state.pc = word _ 0) (running : state.halted = false) (empty : state.heap = #[])
    (input : state.stack = inputWords (SharedDetectorLoop.Width parameters graph (retained parameters graph)) rows roots
        (assignmentOfSet {parameters.bridge.target}) ++
      word _ parameters.bridge.target.val ::
        (SharedRetainedCandidates.masks (SharedDetectorLoop.Width parameters graph (retained parameters graph))
          (assignmentOfSet (extensionBase parameters.buses parameters.bridge.target T))
          ((List.finRange parameters.channels).map (assignmentOfSet F)) ++ suffix)) :
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
  have capacity := SharedMachineCapacity.capacity (retained parameters graph) graph.countedSize
    (selectedSize parameters).total
  change 131072 * (retained parameters graph + graph.countedSize + (selectedSize parameters).total + 1) <
    2 ^ SharedDetectorLoop.Width parameters graph (retained parameters graph) at capacity
  have retainedValue : retained parameters graph =
      480 * (graph.countedSize + 1) + 77 * (selectedSize parameters).total + 1300 := rfl
  have size := graph.countedSize_eq
  have packetValue : packetSize graph =
      5 + 6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length +
        parameters.channels := by simp only [packetSize, maskBase, rootBase]
  have wordsLength := inputWords_length (SharedDetectorLoop.Width parameters graph (retained parameters graph))
    graph rows roots matched rootMatches (assignmentOfSet {parameters.bridge.target})
  have inner := SharedDetectorAssembly.code_length_bound parameters graph T F
    (SharedDetectorLoop.Width parameters graph (retained parameters graph)) rows roots (detectorEntry parameters graph) rootMatches
  have prepared := preparedSize_le graph
  have present : SharedRootRead.BlockAt (program parameters graph T F rows roots) 0
      (code parameters graph T F (SharedDetectorLoop.Width parameters graph (retained parameters graph)) rows roots) := by
    intro offset below
    simp only [program, List.getElem?_toArray, Nat.zero_add]
  unfold code at present
  have parkAt := block_left _ 0 _ _ (block_left _ 0 _ _ present)
  have popAt := block_right _ 0 _ _ (block_left _ 0 _ _ present)
  have detectorAt := block_right _ 0 _ _ present
  simp only [List.length_append, SharedWitnessPark.code_length, List.length_singleton, Nat.zero_add] at popAt detectorAt
  obtain ⟨parked, parkTrace, parkHeap, parkStack, parkOutput, parkPC, parkRunning, parkFrame⟩ :=
    SharedWitnessPark.execution (program parameters graph T F rows roots) state
      (inputWords (SharedDetectorLoop.Width parameters graph (retained parameters graph)) rows roots
        (assignmentOfSet {parameters.bridge.target})) _ 0 position running
      (by rw [wordsLength]; omega) (by rw [empty, wordsLength]; simp; omega) input
      (by rw [wordsLength]; simpa using parkAt)
  obtain ⟨popped, popTrace, popPC, popReg, popHeap, popStack, popOutput, popRunning, popFrame⟩ :=
    pop_execution (program parameters graph T F rows roots) parked (2 * packetSize graph) 4
      (word _ parameters.bridge.target.val) _ (by rw [parkPC, wordsLength]; simp) parkRunning (by omega)
      (by simpa using popAt 0 (by simp)) parkStack
  obtain ⟨answer, final, ticks, peak, trace, halted, decision, time, space, meaning, checked⟩ :=
    SharedDetectorAssembly.execution parameters raw drive graph guarded T F consistent (retained parameters graph)
      (detectorEntry parameters graph) (program parameters graph T F rows roots) rows roots matched heads rootMatches
      observations observationEq suffix popped popPC popRunning
      (by rw [popHeap, parkHeap, empty]; exact inputWords_heap _ rows roots _) popStack popReg
      (by have entryValue : detectorEntry parameters graph = 2 * packetSize graph + 1 := rfl
          omega)
      (by simpa only [detectorEntry] using detectorAt)
  have parkedLive : parked.liveWords = state.liveWords := by
    have heapSize : parked.heap.size = packetSize graph := by
      rw [parkHeap, empty]; simp [wordsLength]
    have stackLength : state.stack.length = packetSize graph + parked.stack.length := by
      rw [input, parkStack]; simp only [List.length_append, wordsLength]
    have stateUnfold : state.liveWords = 8 + state.heap.size + state.stack.length + state.output.length + 1 := rfl
    have parkedUnfold : parked.liveWords = 8 + parked.heap.size + parked.stack.length + parked.output.length + 1 := rfl
    rw [parkOutput] at parkedUnfold
    rw [empty] at stateUnfold
    simp only [Array.size_empty] at stateUnfold
    omega
  have poppedLive : popped.liveWords + 1 = parked.liveWords := by
    simp only [State.liveWords, popHeap, popStack, popOutput, parkStack, List.length_cons]; omega
  have joined := parkTrace.append (popTrace.append trace)
  refine ⟨answer, final, _, _, joined, halted, decision, ?_, ?_, meaning, checked⟩
  · rw [wordsLength]
    have channelPart : parameters.channels * (84 * graph.countedSize + 54) ≤
        parameters.channels * (5100 * (graph.countedSize + 1)) := Nat.mul_le_mul_left _ (by omega)
    have outputSplit : graph.roots.length * (5100 * (graph.countedSize + 1)) =
        graph.roots.length * (5032 * (graph.countedSize + 1)) + graph.roots.length * (68 * (graph.countedSize + 1)) := by
      rw [← Nat.mul_add]; congr 1; omega
    have outputLinear : graph.roots.length * 10 ≤ graph.roots.length * (68 * (graph.countedSize + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    cases answer <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at time ⊢ <;> omega
  · simp only [max_le_iff]
    omega

end Controller.Cost.SharedDetectorCold
