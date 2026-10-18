module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedCandidateStep

@[expose] public section

/-! One resident candidate loop reuses the graph and consumes exclusion bits in channel order. -/
namespace Controller.Cost.SharedHeadLoop
open Controller.Decoder Controller.Decoder.DAG Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.RawTransferLoops

@[irreducible] def code (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) : Program width 8 :=
  SharedHeadControl.header width entry done n ++
    (SharedCandidateStep.code width n rows roots (entry + 3) ++ SharedHeadControl.tail width entry)

@[simp] theorem code_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat) :
    (code width n rows roots entry done).size = 2 * roots.length + 209 := by unfold code; simp; omega

theorem zero_execution (resident : Program width 8) (state : State width 8)
    (n : Nat) (rows : List Row) (roots : List Nat) (entry done : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 * roots.length + 209 < 2 ^ width) (nFits : n < 2 ^ width)
    (held : state.reg 4 = word width n)
    (physical : CodeAt resident entry (code width n rows roots entry done)) :
    ∃ final, Execution resident state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 4 = word width n := by
  have all := physical
  unfold code at all
  have headerCode := RawSharedOrdered.takePrefix resident entry _ _ all
  obtain ⟨final, trace, heap, stack, output, pc, active, frame⟩ :=
    SharedHeadControl.header_execution resident state entry done n n position running
      (by omega) nFits nFits held headerCode
  exact ⟨final, trace, heap, stack, output, by simpa using pc, active,
    (frame 4 (by decide)).trans held⟩

set_option maxHeartbeats 2000000 in
theorem iteration_execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n) (channel : Fin n) (excluded : Bool)
    (witnesses suffix : List (Word width)) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry done))
    (room : entry + 2 * roots.length + 209 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values)
    (input : state.stack = witnesses ++ boolWord width excluded :: suffix)
    (lengths : witnesses.length = graph.roots.length) (held : state.reg 4 = word width channel.val) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧ ticks ≤ 84 * graph.countedSize + 54 ∧
      peak ≤ 8 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = state.heap ∧
      final.stack = (if values channel || excluded then witnesses else
        SharedRootAggregate.updated (word width channel.val)
          (graph.roots.map (fun root => (root.val, graph.eval (SharedCandidateProbe.enabled values channel) root))) witnesses) ++ suffix ∧
      final.output = state.output ∧ final.pc = word width entry ∧ final.halted = false ∧
      final.reg 4 = word width (channel.val + 1) := by
  have size := graph.countedSize_eq
  have nFits : n < 2 ^ width := by omega
  have all := physical
  unfold code at all
  have headerCode := RawSharedOrdered.takePrefix resident entry _ _ all
  have rest := RawSharedOrdered.takeSuffix resident entry _ _ all
  have bodyCode := RawSharedOrdered.takePrefix resident (entry + 3) _ _ (by simpa using rest)
  have tailCode := RawSharedOrdered.takeSuffix resident (entry + 3) _ _ (by simpa using rest)
  obtain ⟨ready, headerTrace, readyHeap, readyStack, readyOutput, readyPC, readyRunning, readyFrame⟩ :=
    SharedHeadControl.header_execution resident state entry done n channel.val position running
      (by omega) nFits (by omega) held headerCode
  obtain ⟨body, bodyTicks, bodyPeak, bodyTrace, bodyTime, bodySpace, bodyHeap,
    bodyStack, bodyOutput, bodyPC, bodyRunning, bodyHead⟩ :=
    SharedCandidateStep.execution resident ready graph rows roots matched heads rootMatches values channel excluded
      witnesses suffix (entry + 3) capacity bodyCode (by omega)
      (by simpa only [ite_eq_right (by omega : channel.val ≠ n)] using readyPC) readyRunning
      (readyHeap.trans heapStored) (readyStack.trans input) lengths ((readyFrame 4 (by decide)).trans held)
  obtain ⟨final, tailTrace, finalHead, finalHeap, finalStack, finalOutput, finalPC, finalRunning, finalFrame⟩ :=
    SharedHeadControl.tail_execution resident body (entry + 3 + 2 * roots.length + 202) entry channel.val
      bodyPC bodyRunning (by omega) (by omega) bodyHead
      (by simpa only [SharedCandidateStep.code_size, Nat.add_assoc] using tailCode)
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, readyHeap, readyStack, readyOutput]
  have initialSpace := SharedGraphRound.live_bound state graph rows roots matched rootMatches values heapStored
  have bodyLive : body.liveWords ≤ bodyPeak := Execution.final_storage_le bodyTrace
  have joined := headerTrace.append (bodyTrace.append tailTrace)
  refine ⟨final, 3 + (bodyTicks + 4), max state.liveWords (max bodyPeak body.liveWords), joined,
    by omega, ?_, finalHeap.trans (bodyHeap.trans readyHeap), finalStack.trans bodyStack,
    finalOutput.trans (bodyOutput.trans readyOutput), finalPC, finalRunning, finalHead⟩
  simp only [readyStack, readyOutput] at bodySpace
  apply Nat.max_le.mpr
  constructor
  · omega
  · apply Nat.max_le.mpr
    constructor <;> omega

def witnessStep (graph : DAG n) (values : Assignment n) (head : Nat)
    (excluded : Bool) (witnesses : List (Word width)) : List (Word width) :=
  if bound : head < n then
    let channel : Fin n := ⟨head, bound⟩
    if values channel || excluded then witnesses else
      SharedRootAggregate.updated (word width head)
        (graph.roots.map (fun root => (root.val, graph.eval (SharedCandidateProbe.enabled values channel) root))) witnesses
  else witnesses

def witnessFold (graph : DAG n) (values : Assignment n) (head : Nat)
    (flags : List Bool) (witnesses : List (Word width)) : List (Word width) :=
  match flags with
  | [] => witnesses
  | flag :: rest => witnessFold graph values (head + 1) rest (witnessStep graph values head flag witnesses)

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (head : Nat) (flags : List Bool) (witnesses suffix : List (Word width)) (entry done : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (code width n rows roots entry done))
    (room : entry + 2 * roots.length + 209 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values)
    (input : state.stack = witnesses ++ flags.map (boolWord width) ++ suffix)
    (lengths : witnesses.length = graph.roots.length) (held : state.reg 4 = word width head)
    (remaining : head + flags.length = n) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ flags.length * (84 * graph.countedSize + 54) + 3 ∧
      peak ≤ 8 * graph.countedSize + 18 + state.stack.length + state.output.length ∧
      final.heap = state.heap ∧
      final.stack = witnessFold graph values head flags witnesses ++ suffix ∧
      final.output = state.output ∧ final.pc = word width done ∧ final.halted = false ∧
      final.reg 4 = word width n := by
  induction flags generalizing state head witnesses with
  | nil =>
    have headEq : head = n := by simpa using remaining
    obtain ⟨final, trace, heap, stack, output, pc, active, reg⟩ :=
      zero_execution resident state n rows roots entry done position running room
        (by have size := graph.countedSize_eq; omega) (by simpa [headEq] using held) physical
    have space := SharedGraphRound.live_bound state graph rows roots matched rootMatches values heapStored
    exact ⟨final, 3, state.liveWords, trace, by simp, by omega, heap,
      by simpa [witnessFold, input] using stack, output, pc, active, reg⟩
  | cons flag flags ih =>
    have bound : head < n := by simp only [List.length_cons] at remaining; omega
    let channel : Fin n := ⟨head, bound⟩
    obtain ⟨middle, stepTicks, stepPeak, stepTrace, stepTime, stepSpace, middleHeap,
      middleStack, middleOutput, middlePC, middleRunning, middleHead⟩ :=
      iteration_execution resident state graph rows roots matched heads rootMatches values channel flag
        witnesses (flags.map (boolWord width) ++ suffix) entry done capacity physical room position running
        heapStored (by simpa [List.map_cons, List.append_assoc] using input) lengths held
    have middleStack' : middle.stack = witnessStep graph values head flag witnesses ++
        flags.map (boolWord width) ++ suffix := by
      simpa [witnessStep, bound, channel, List.append_assoc] using middleStack
    have newLengths : (witnessStep graph values head flag witnesses).length = graph.roots.length := by
      simp only [witnessStep, dite_eq_left bound]
      split
      · exact lengths
      · simp [SharedRootAggregate.updated, List.length_zipWith, lengths]
    obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, finalHeap,
      finalStack, finalOutput, finalPC, finalRunning, finalHead⟩ :=
      ih middle (head + 1) (witnessStep graph values head flag witnesses) middlePC middleRunning
        (middleHeap.trans heapStored) middleStack' newLengths middleHead
        (by simp only [List.length_cons] at remaining; omega)
    have stackSize : middle.stack.length ≤ state.stack.length := by
      simp only [middleStack', List.length_append, List.length_map, newLengths]
      rw [input]
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    refine ⟨final, stepTicks + restTicks, max stepPeak restPeak, stepTrace.append restTrace,
      ?_, Nat.max_le.mpr ⟨stepSpace, ?_⟩, finalHeap.trans middleHeap,
      ?_, finalOutput.trans middleOutput, finalPC, finalRunning, finalHead⟩
    · simp only [List.length_cons, Nat.add_mul]; omega
    · rw [middleOutput] at restSpace; omega
    · simpa only [witnessFold] using finalStack

end Controller.Cost.SharedHeadLoop
