module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedTableProbe

@[expose] public section

/-! Singleton columns of a node-value table. Each column is evaluated once,
saved on the stack and followed by a reset of the reused input/value heap. -/
namespace Controller.Cost.SharedTableBatch
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.ForestInputPrefixStored Controller.Cost.ForestInputStored
open Controller.Cost.UniformDAGRun Controller.Cost.RawTransferLoops

def single (channel : Fin n) : Assignment n := SharedCandidateProbe.enabled (fun _ => false) channel

def stepCode (width n : Nat) (rows : List Row) (roots : List Nat) (channel : Fin n) (entry : Nat) : Program width 8 :=
  #[.constant 4 (word width channel.val)] ++
    (SharedCandidateSet.code width (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size true ++
      (SharedTableProbe.code width n rows roots (entry + 5) (entry + 148) ++
        SharedCandidateSet.code width (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size false))

@[simp] theorem stepCode_size (width n : Nat) (rows : List Row) (roots : List Nat) (channel : Fin n) (entry : Nat) :
    (stepCode width n rows roots channel entry).size = 152 := by simp [stepCode]

set_option maxHeartbeats 400000 in
theorem step_execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (channel : Fin n) (entry : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (stepCode width n rows roots channel entry))
    (room : entry + 152 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => false)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 53 * graph.countedSize + 24 ∧ peak ≤ state.liveWords + 2 * graph.nodeCount + 4 ∧
      final.heap = state.heap ∧ final.stack = SharedTableProbe.words graph (single channel) width ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 152) ∧ final.halted = false := by
  have all := physical
  unfold stepCode at all
  have firstAt := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailAt := RawSharedOrdered.takeSuffix resident entry _ _ all
  have tailAt' : CodeAt resident (entry + 1)
      (SharedCandidateSet.code width (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size true ++
        (SharedTableProbe.code width n rows roots (entry + 5) (entry + 148) ++
          SharedCandidateSet.code width (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size false)) := by
    simpa using tailAt
  have enableAt := RawSharedOrdered.takePrefix resident (entry + 1) _ _ tailAt'
  have middleAt := RawSharedOrdered.takeSuffix resident (entry + 1) _ _ tailAt'
  have middleAt' : CodeAt resident (entry + 5)
      (SharedTableProbe.code width n rows roots (entry + 5) (entry + 148) ++
        SharedCandidateSet.code width (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size false) := by
    simpa only [SharedCandidateSet.code_size, Nat.add_assoc, Nat.reduceAdd] using middleAt
  have probeAt := RawSharedOrdered.takePrefix resident (entry + 5) _ _ middleAt'
  have resetAt := RawSharedOrdered.takeSuffix resident (entry + 5) _ _ middleAt'
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  let source := cacheHeap width (packetHeaderHeap width n rows roots) rows roots
  have tableFits : source.size + n < 2 ^ width := by
    dsimp only [source]
    simp only [cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount]
    omega
  obtain ⟨addressed, addressTrace, addressPC, addressValue, addressHeap, addressStack,
      addressOutput, addressRunning, _⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry channel.val 4 state position running (by omega)
      (by simpa using firstAt ⟨0, by simp⟩)
  obtain ⟨enabled, enableTrace, enableHeap, enableStack, enableOutput, enablePC, enableRunning, enableFrame⟩ :=
    SharedCandidateSet.execution resident addressed source (fun _ : Fin n => false) channel true (entry + 1)
      addressPC addressRunning (by omega) tableFits (addressHeap.trans heapStored) addressValue enableAt
  have enabledHeap : enabled.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots (single channel) := enableHeap
  obtain ⟨sampled, sampleTicks, samplePeak, sampleTrace, sampleTime, sampleSpace,
      sampleHeap, sampleStack, sampleOutput, samplePC, sampleRunning, sampleHead⟩ :=
    SharedTableProbe.execution resident enabled graph rows roots matched heads rootMatches (single channel)
      (entry + 5) (entry + 148) capacity probeAt (by omega)
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using enablePC) enableRunning enabledHeap
  have sampledHeap : sampled.heap = withValues source (single channel) := sampleHeap.trans enabledHeap
  have sampledHead : sampled.reg 4 = word width channel.val :=
    sampleHead.trans ((enableFrame 4 (by decide) (by decide)).trans addressValue)
  obtain ⟨final, resetTrace, resetHeap, resetStack, resetOutput, resetPC, resetRunning, _⟩ :=
    SharedCandidateSet.execution resident sampled source (single channel) channel false (entry + 148)
      samplePC sampleRunning (by omega) tableFits sampledHeap sampledHead
      (by simpa only [SharedTableProbe.code_size, Nat.add_assoc, Nat.reduceAdd] using resetAt)
  have originalHeap : final.heap = state.heap := by
    have reset := SharedCandidateProbe.reset_enabled (fun _ : Fin n => false) channel rfl
    unfold single at resetHeap
    rw [reset] at resetHeap
    exact resetHeap.trans heapStored.symm
  have addressLive : addressed.liveWords = state.liveWords := by
    simp only [State.liveWords, addressHeap, addressStack, addressOutput]
  have enabledLive : enabled.liveWords = state.liveWords := by
    simp only [State.liveWords, enableHeap, heapStored, channelHeap, withValues_size,
      enableStack, enableOutput, addressStack, addressOutput, source]
  have sampledLive : sampled.liveWords = state.liveWords + graph.nodeCount := by
    simp only [State.liveWords, sampleHeap, sampleStack, sampleOutput, SharedTableProbe.words_length,
      List.length_append, enabledHeap, heapStored, channelHeap, withValues_size,
      enableStack, enableOutput, addressStack, addressOutput]
    omega
  refine ⟨final, 1 + (4 + (sampleTicks + 4)),
    max state.liveWords (max addressed.liveWords (max samplePeak sampled.liveWords)),
    addressTrace.append (enableTrace.append (sampleTrace.append resetTrace)), by omega, ?_, originalHeap,
    ?_, resetOutput.trans (sampleOutput.trans (enableOutput.trans addressOutput)), ?_, resetRunning⟩
  · rw [enabledLive] at sampleSpace
    rw [addressLive, sampledLive]
    omega
  · rw [resetStack, sampleStack, enableStack, addressStack]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using resetPC

def code (width n : Nat) (rows : List Row) (roots : List Nat) : Nat → List (Fin n) → Program width 8
  | _, [] => #[]
  | entry, channel :: rest => stepCode width n rows roots channel entry ++ code width n rows roots (entry + 152) rest

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) (ids : List (Fin n)) :
    (code width n rows roots entry ids).size = 152 * ids.length := by
  induction ids generalizing entry with
  | nil => simp [code]
  | cons channel rest ih => simp [code, ih]; omega

def columns (graph : DAG n) (ids : List (Fin n)) (width : Nat) : List (Word width) :=
  ids.reverse.flatMap (fun channel => SharedTableProbe.words graph (single channel) width)

@[simp] theorem columns_length (graph : DAG n) (ids : List (Fin n)) :
    (columns graph ids width).length = ids.length * graph.nodeCount := by
  have all : ∀ xs : List (Fin n),
      (xs.flatMap (fun channel => SharedTableProbe.words graph (single channel) width)).length =
        xs.length * graph.nodeCount := by
    intro xs
    induction xs with
    | nil => simp
    | cons channel rest ih => simp [ih, Nat.add_mul, Nat.add_comm]
  simpa only [columns, List.length_reverse] using all ids.reverse

set_option maxHeartbeats 400000 in
theorem execution (resident : Program width 8) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (ids : List (Fin n)) (entry : Nat) (state : State width 8)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry ids))
    (room : entry + 152 * ids.length < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => false)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ ids.length * (53 * graph.countedSize + 24) ∧
      peak ≤ state.liveWords + (ids.length + 1) * graph.nodeCount + 4 ∧
      final.heap = state.heap ∧ final.stack = columns graph ids width ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 152 * ids.length) ∧ final.halted = false := by
  induction ids generalizing entry state with
  | nil => exact ⟨state, 0, state.liveWords, Execution.refl state, by simp, by omega, rfl,
      by simp [columns], rfl, by simpa using position, running⟩
  | cons channel rest ih =>
    have firstAt := RawSharedOrdered.takePrefix resident entry _ _ physical
    have tailAt := RawSharedOrdered.takeSuffix resident entry _ _ physical
    obtain ⟨next, firstTicks, firstPeak, firstTrace, firstTime, firstSpace, firstHeap, firstStack,
        firstOutput, firstPC, firstRunning⟩ :=
      step_execution resident state graph rows roots matched heads rootMatches channel entry capacity firstAt
        (by simp only [List.length_cons] at room; omega) position running heapStored
    obtain ⟨final, tailTicks, tailPeak, tailTrace, tailTime, tailSpace, finalHeap, finalStack,
        finalOutput, finalPC, finalRunning⟩ :=
      ih (entry + 152) next (by simpa only [code, stepCode_size] using tailAt)
        (by simp only [List.length_cons] at room; omega) firstPC firstRunning (firstHeap.trans heapStored)
    have nextLive : next.liveWords = state.liveWords + graph.nodeCount := by
      simp only [State.liveWords, firstHeap, firstStack, firstOutput, List.length_append, SharedTableProbe.words_length]
      omega
    refine ⟨final, firstTicks + tailTicks, max firstPeak tailPeak, firstTrace.append tailTrace,
      ?_, ?_, finalHeap.trans firstHeap, ?_, finalOutput.trans firstOutput, ?_, finalRunning⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · rw [nextLive] at tailSpace
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at tailSpace ⊢
      omega
    · rw [finalStack, firstStack]
      simp [columns, List.reverse_cons, List.flatMap_append, List.append_assoc]
    · simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPC

end Controller.Cost.SharedTableBatch
