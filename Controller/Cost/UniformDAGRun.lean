module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.UniformDAGLoop

@[expose] public section

/-! Executed topological iteration, joining the fixed loop control and the
packet-derived node executor. Saved loop frames are consumed by actual pops;
no register reset or semantic transition replaces a fetched instruction. -/
namespace Controller.Cost.UniformDAGRun
open Controller.Cost.GateProgram Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGSource

private theorem blocks (program : Program width 4) (base countAddress : ℕ)
    (layout : UniformDAGNode.Layout)
    (block : BlockAt program base (UniformDAGLoop.code width base countAddress layout)) :
    BlockAt program (base + 4) (UniformDAGLoop.enterCode width (base + 126)) ∧
    BlockAt program (base + 117) (UniformDAGLoop.advanceCode width (base + 4)) := by
  have afterInit := BlockAt.suffix program base (UniformDAGLoop.initializeCode width countAddress)
    (UniformDAGLoop.enterCode width (base + 126) ++
      (UniformDAGNode.code width (base + 8) layout ++ UniformDAGLoop.advanceCode width (base + 4))) block
  have entered : BlockAt program (base + 4)
      (UniformDAGLoop.enterCode width (base + 126) ++
        (UniformDAGNode.code width (base + 8) layout ++ UniformDAGLoop.advanceCode width (base + 4))) := by
    simpa only [UniformDAGLoop.initializeCode_length] using afterInit
  have enterBlock := BlockAt.prefix program (base + 4) (UniformDAGLoop.enterCode width (base + 126))
    (UniformDAGNode.code width (base + 8) layout ++ UniformDAGLoop.advanceCode width (base + 4)) entered
  have afterEnter : BlockAt program (base + 8)
      (UniformDAGNode.code width (base + 8) layout ++ UniformDAGLoop.advanceCode width (base + 4)) := by
    simpa only [UniformDAGLoop.enterCode_length, Nat.add_assoc] using
      BlockAt.suffix program (base + 4) (UniformDAGLoop.enterCode width (base + 126)) _ entered
  have tail := BlockAt.suffix program (base + 8) (UniformDAGNode.code width (base + 8) layout)
    (UniformDAGLoop.advanceCode width (base + 4)) afterEnter
  exact ⟨enterBlock, by simpa only [UniformDAGNode.code_length, Nat.add_assoc] using tail⟩

/-- One complete fetched iteration appends the exact next value and returns
with the decremented count and advanced original row offset. -/
theorem iteration (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (node : Fin graph.nodeCount) (channels : Channel n → Bool) (earlier : Fin node.val → Bool)
    (physical : state.heap = evaluationHeap heap rows roots channels earlier)
    (offset : state.reg 3 = word width (2 * node.val))
    (remaining : ℕ) (positive : 0 < remaining) (countFits : remaining < 2 ^ width)
    (suffix : List (Word width)) (stack : state.stack = word width remaining :: suffix)
    (base countAddress : ℕ) (pc : state.pc = word width (base + 4))
    (running : state.halted = false) (fits : base + 126 < 2 ^ width)
    (room : state.heap.size < 2 ^ width)
    (block : BlockAt program base
      (UniformDAGLoop.code width base countAddress (UniformDAGTypedNode.layout heap rows roots channels))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 43 + 18 * ((graph.node node).children.length + (graph.node node).guardLabels.length) ∧
      peak ≤ state.liveWords + 3 ∧
      final.heap = state.heap.push (boolWord width ((graph.node node).eval channels earlier)) ∧
      final.stack = word width (remaining - 1) :: suffix ∧ final.output = state.output ∧
      final.reg 3 = word width (2 * (node.val + 1)) ∧
      final.pc = word width (base + 4) ∧ final.halted = false := by
  obtain ⟨enterBlock, tailBlock⟩ := blocks program base countAddress _ block
  obtain ⟨ready, entryPeak, et, ep, eh, eo, es, er3, ePC, er⟩ :=
    UniformDAGLoop.enter_execution program state (base + 4) (base + 126) remaining suffix
      positive countFits stack pc running (by omega) enterBlock
  have entryLive : ready.liveWords = state.liveWords + 1 := by
    simp [State.liveWords, eh, eo, es, stack]; omega
  obtain ⟨allocated, nodeTicks, nodePeak, nt, np, ns, nh, nst, no, nPC, nr⟩ :=
    UniformDAGTypedNode.execution program ready heap graph rows roots matched heads node channels earlier
      (eh.trans physical) (er3.trans offset) (base + 8)
      (by simpa only [Nat.add_assoc] using ePC) er (by omega)
      (by simpa only [eh] using room) (UniformDAGLoop.node_block program base countAddress _ block)
  have offsetFits : 2 * node.val + 2 < 2 ^ width := by
    have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    rw [physical, evaluationHeap_size, cacheHeap_size] at room
    omega
  obtain ⟨final, tailPeak, atTrace, ap, ah, ao, ast, ar3, aPC, ar⟩ :=
    UniformDAGLoop.advance_execution program allocated (base + 117) (base + 4)
      (2 * node.val) remaining suffix positive countFits offsetFits
      (by simpa only [nst, es, offset])
      (by simpa only [Nat.add_assoc] using nPC) nr (by omega) tailBlock
  have allocatedLive : allocated.liveWords = state.liveWords + 2 := by
    simp [State.liveWords, nh, nst, eh, es, no, eo, stack]; omega
  refine ⟨final, 4 + nodeTicks + 9, max (max entryPeak nodePeak) tailPeak,
    ?_, ?_, ?_, ?_, ast, ao.trans (no.trans eo), ?_, aPC, ar⟩
  · simpa using (et.append nt).append atTrace
  · omega
  · rw [entryLive] at ns
    rw [allocatedLive] at ap
    simp only [max_le_iff]
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · simpa only [ah, nh, eh]
  · simpa only [Nat.mul_add, Nat.mul_one] using ar3


private theorem fetched (program : Program width 4) (state : State width 4)
    (address : ℕ) (instruction : Instruction width 4)
    (pc : state.pc = word width address) (fits : address < 2 ^ width)
    (entry : program[address]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [pc, show (word width address).val = address from Nat.mod_eq_of_lt fits, entry]
  rfl

/-- Fetch the packet count and establish the loop frame by four instructions. -/
theorem initialize_execution (program : Program width 4) (state : State width 4)
    (base address count : ℕ) (addressFits : address < 2 ^ width)
    (addressBound : address < state.heap.size)
    (stored : state.heap[address] = word width count)
    (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 4 < 2 ^ width)
    (block : BlockAt program base (UniformDAGLoop.initializeCode width address)) :
    ∃ ready peak, Execution program state ready 4 peak ∧ peak ≤ state.liveWords + 1 ∧
      ready.heap = state.heap ∧ ready.output = state.output ∧
      ready.stack = word width count :: state.stack ∧ ready.reg 3 = word width 0 ∧
      ready.pc = word width (base + 4) ∧ ready.halted = false := by
  let s1 := state.advance.put 0 (word width address)
  let s2 := s1.advance.put 0 (word width count)
  let s3 := { s2.advance with stack := s2.reg 0 :: s2.stack }
  let s4 := s3.advance.put 3 (word width 0)
  have pv : state.pc.val = base := by rw [pc]; exact Nat.mod_eq_of_lt (by omega)
  have av : (word width address).val = address := Nat.mod_eq_of_lt addressFits
  have p1 : s1.pc = word width (base + 1) := by simp [s1, State.advance, State.put, pv]
  have v1 : s1.pc.val = base + 1 := by rw [p1]; exact Nat.mod_eq_of_lt (by omega)
  have p2 : s2.pc = word width (base + 2) := by simp [s2, State.advance, State.put, v1, Nat.add_assoc]
  have v2 : s2.pc.val = base + 2 := by rw [p2]; exact Nat.mod_eq_of_lt (by omega)
  have p3 : s3.pc = word width (base + 3) := by simp [s3, State.advance, v2, Nat.add_assoc]
  have v3 : s3.pc.val = base + 3 := by rw [p3]; exact Nat.mod_eq_of_lt (by omega)
  have first : programStep program state = some s1 := by
    rw [fetched program state base (.constant 0 (word width address)) pc (by omega)
      (by simpa [UniformDAGLoop.initializeCode] using block 0 (by simp [UniformDAGLoop.initializeCode]))]
    simp [step, s1, running]
  have second : programStep program s1 = some s2 := by
    rw [fetched program s1 (base + 1) (.load 0 0) p1 (by omega)
      (by simpa [UniformDAGLoop.initializeCode] using block 1 (by simp [UniformDAGLoop.initializeCode]))]
    simp [step, s1, s2, State.advance, State.put, running, av, addressBound, stored]
  have third : programStep program s2 = some s3 := by
    rw [fetched program s2 (base + 2) (.push 0) p2 (by omega)
      (by simpa [UniformDAGLoop.initializeCode] using block 2 (by simp [UniformDAGLoop.initializeCode]))]
    simp [step, s1, s2, s3, State.advance, State.put, running]
  have fourth : programStep program s3 = some s4 := by
    rw [fetched program s3 (base + 3) (.constant 3 (word width 0)) p3 (by omega)
      (by simpa [UniformDAGLoop.initializeCode] using block 3 (by simp [UniformDAGLoop.initializeCode]))]
    simp [step, s1, s2, s3, s4, State.advance, State.put, running]
  have trace := Execution.cons first (Execution.cons second
    (Execution.cons third (Execution.cons fourth (Execution.refl s4))))
  refine ⟨s4, _, by simpa using trace, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [max_le_iff]
    simp [s1, s2, s3, s4, State.liveWords, State.advance, State.put]
    omega
  · simp [s1, s2, s3, s4, State.advance, State.put]
  · simp [s4, State.put]
  · simp [s4, State.advance, State.put, v3, Nat.add_assoc]
  · simp [s1, s2, s3, s4, State.advance, State.put, running]

def weights (graph : DAG n) : List ℕ :=
  List.ofFn (fun index : Fin graph.nodeCount =>
    43 + 18 * ((graph.node index).children.length + (graph.node index).guardLabels.length))

@[simp] theorem weights_length (graph : DAG n) : (weights graph).length = graph.nodeCount := by
  simp [weights]


/-- Every stored child and guard occurrence contributes its actual scan cost. -/
theorem weights_sum (graph : DAG n) :
    (weights graph).sum = 43 * graph.nodeCount +
      18 * (graph.childIncidences + graph.guardIncidences) := by
  simp only [weights, DAG.childIncidences, DAG.guardIncidences, List.sum_ofFn]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

private theorem extended_heap (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (channels : Channel n → Bool)
    (k : ℕ) (bound : k ≤ graph.nodeCount) (nextBound : k + 1 ≤ graph.nodeCount) :
    evaluationHeap heap rows roots channels (graph.evalPrefix channels (k + 1) nextBound) =
      (evaluationHeap heap rows roots channels (graph.evalPrefix channels k bound)).push
        (boolWord width ((graph.node ⟨k, by omega⟩).eval channels (graph.evalPrefix channels k bound))) := by
  simpa only [evaluationHeap, DAG.evalPrefix] using
    append_value (channelHeap heap rows roots channels) (graph.evalPrefix channels k bound)
      ((graph.node ⟨k, by omega⟩).eval channels (graph.evalPrefix channels k bound))

/-- The whole remaining decoder suffix follows actual loop backedges and
allocates its complete topological table. No node is skipped or revisited. -/
theorem suffix_execution (program : Program width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (channels : Channel n → Bool) (base countAddress : ℕ)
    (fits : base + 126 < 2 ^ width)
    (room : (cacheHeap width heap rows roots).size + n + graph.nodeCount ≤ 2 ^ width)
    (block : BlockAt program base
      (UniformDAGLoop.code width base countAddress (UniformDAGTypedNode.layout heap rows roots channels))) :
    ∀ remaining k, (total : k + remaining = graph.nodeCount) →
      (bound : k ≤ graph.nodeCount) → (state : State width 4) →
      state.heap = evaluationHeap heap rows roots channels (graph.evalPrefix channels k bound) →
      state.reg 3 = word width (2 * k) →
      (suffix : List (Word width)) → state.stack = word width remaining :: suffix →
      state.pc = word width (base + 4) → state.halted = false →
      ∃ final ticks peak, Execution program state final ticks peak ∧
        ticks ≤ ((weights graph).drop k).sum + 2 ∧ peak ≤ state.liveWords + remaining + 3 ∧
        final.heap = evaluationHeap heap rows roots channels (graph.evalTable channels) ∧
        final.stack = suffix ∧ final.output = state.output ∧
        final.pc = word width (base + 126) ∧ final.halted = false := by
  intro remaining
  induction remaining with
  | zero =>
      intro k total bound state physical offset suffix stack pc running
      have atEnd : k = graph.nodeCount := by omega
      subst k
      obtain ⟨enterBlock, tailBlock⟩ := blocks program base countAddress _ block
      obtain ⟨final, peak, trace, space, fh, fo, fs, fp, fr⟩ :=
        UniformDAGLoop.exit_execution program state (base + 4) (base + 126) suffix
          stack pc running (by omega) enterBlock
      refine ⟨final, 2, peak, trace, ?_, by omega, ?_, fs, fo, fp, fr⟩
      · have empty : (weights graph).drop graph.nodeCount = [] := by
          simpa only [weights_length] using (List.drop_length (l := weights graph))
        simp only [empty, List.sum_nil, Nat.zero_add, le_refl]
      · simpa only [DAG.evalTable] using fh.trans physical
  | succ remaining ih =>
      intro k total bound state physical offset suffix stack pc running
      have valid : k < graph.nodeCount := by omega
      let node : Fin graph.nodeCount := ⟨k, valid⟩
      have nextBound : k + 1 ≤ graph.nodeCount := by omega
      have countFits : remaining + 1 < 2 ^ width := by
        have rowBound : k < rows.length := by rw [matched.length_eq]; exact valid
        have sizes := cacheHeap_size heap rows roots
        rw [matched.length_eq] at sizes
        omega
      have stateRoom : state.heap.size < 2 ^ width := by
        rw [physical, evaluationHeap_size]; omega
      obtain ⟨next, ticks, peak, trace, time, space, nh, ns, no, nr3, np, nr⟩ :=
        iteration program state heap graph rows roots matched heads node channels
          (graph.evalPrefix channels k bound) physical offset (remaining + 1) (by omega) countFits
          suffix stack base countAddress pc running fits stateRoom block
      have nextPhysical : next.heap =
          evaluationHeap heap rows roots channels (graph.evalPrefix channels (k + 1) nextBound) := by
        rw [extended_heap heap graph rows roots channels k bound nextBound]
        simpa only [node, physical] using nh
      obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, fh, fs, fo, fp, fr⟩ :=
        ih (k + 1) (by omega) nextBound next nextPhysical nr3 suffix
          (by simpa only [Nat.add_sub_cancel] using ns) np nr
      have nextLive : next.liveWords = state.liveWords + 1 := by
        simp [State.liveWords, nh, ns, no, stack]; omega
      have validWeight : k < (weights graph).length := by simpa only [weights_length] using valid
      have split := List.drop_eq_getElem_cons validWeight
      have weight : (weights graph)[k]'validWeight =
          43 + 18 * ((graph.node node).children.length + (graph.node node).guardLabels.length) := by
        simp only [weights, List.getElem_ofFn, node]
      have sumSplit : ((weights graph).drop k).sum =
          43 + 18 * ((graph.node node).children.length + (graph.node node).guardLabels.length) +
            ((weights graph).drop (k + 1)).sum := by
        rw [split, List.sum_cons, weight]
      refine ⟨final, ticks + restTicks, max peak restPeak, trace.append restTrace,
        ?_, ?_, fh, fs, fo.trans no, fp, fr⟩
      · omega
      · rw [nextLive] at restSpace
        simp only [max_le_iff]
        exact ⟨by omega, by omega⟩


/-- Execute the loaded packet count, every topological node, and the terminal
loop test while retaining the caller's stack and output. -/
theorem execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (channels : Channel n → Bool) (base countAddress : ℕ)
    (physical : state.heap = evaluationHeap heap rows roots channels
      (graph.evalPrefix channels 0 (Nat.zero_le _)))
    (countAddressFits : countAddress < 2 ^ width)
    (countAddressBound : countAddress < state.heap.size)
    (stored : state.heap[countAddress] = word width graph.nodeCount)
    (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 126 < 2 ^ width)
    (room : (cacheHeap width heap rows roots).size + n + graph.nodeCount ≤ 2 ^ width)
    (block : BlockAt program base
      (UniformDAGLoop.code width base countAddress (UniformDAGTypedNode.layout heap rows roots channels))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ (weights graph).sum + 6 ∧ peak ≤ state.liveWords + graph.nodeCount + 4 ∧
      final.heap = evaluationHeap heap rows roots channels (graph.evalTable channels) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 126) ∧ final.halted = false := by
  have initialBlock := BlockAt.prefix program base (UniformDAGLoop.initializeCode width countAddress)
    (UniformDAGLoop.enterCode width (base + 126) ++
      (UniformDAGNode.code width (base + 8) (UniformDAGTypedNode.layout heap rows roots channels) ++
        UniformDAGLoop.advanceCode width (base + 4))) block
  obtain ⟨ready, entryPeak, startTrace, startSpace, rh, ro, rs, rr3, rp, rr⟩ :=
    initialize_execution program state base countAddress graph.nodeCount countAddressFits
      countAddressBound stored pc running (by omega) initialBlock
  obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, fh, fs, fo, fp, fr⟩ :=
    suffix_execution program heap graph rows roots matched heads channels base countAddress fits room
      block graph.nodeCount 0 (by omega) (Nat.zero_le _) ready (rh.trans physical)
      (by simpa using rr3) state.stack rs rp rr
  have readyLive : ready.liveWords = state.liveWords + 1 := by
    simp [State.liveWords, rh, ro, rs]
    omega
  refine ⟨final, 4 + restTicks, max entryPeak restPeak, startTrace.append restTrace,
    ?_, ?_, fh, fs, fo.trans ro, fp, fr⟩
  · simp only [List.drop_zero] at restTime
    omega
  · rw [readyLive] at restSpace
    simp only [max_le_iff]
    exact ⟨by omega, by omega⟩


/-- The declared channel words are consumed once by actual loads before the
shared node interpreter; channel storage is included in the initial input. -/
theorem channels_execution (program : Program width 4) (state : State width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (channels : Channel n → Bool) (suffix : List (Word width)) (base countAddress : ℕ)
    (physical : state.heap = cacheHeap width heap rows roots)
    (input : state.stack = (List.ofFn (fun i => boolWord width (channels i))) ++ suffix)
    (countAddressFits : countAddress < 2 ^ width)
    (countAddressBound : countAddress < state.heap.size)
    (stored : state.heap[countAddress] = word width graph.nodeCount)
    (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 2 * n + 126 < 2 ^ width)
    (room : (cacheHeap width heap rows roots).size + n + graph.nodeCount ≤ 2 ^ width)
    (loadBlock : BlockAt program base (InputLoad.code (width := width) n))
    (evalBlock : BlockAt program (base + 2 * n)
      (UniformDAGLoop.code width (base + 2 * n) countAddress
        (UniformDAGTypedNode.layout heap rows roots channels))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 2 * n + 43 * graph.nodeCount +
        18 * (graph.childIncidences + graph.guardIncidences) + 6 ∧
      peak ≤ state.liveWords + graph.nodeCount + 4 ∧
      final.heap = evaluationHeap heap rows roots channels (graph.evalTable channels) ∧
      final.stack = suffix ∧ final.output = state.output ∧
      final.pc = word width (base + 2 * n + 126) ∧ final.halted = false := by
  let values := List.ofFn (fun i : Channel n => boolWord width (channels i))
  have length : values.length = n := by simp [values]
  obtain ⟨loaded, loadTrace, lh, ls, lo, lp, lr⟩ :=
    InputLoad.code_execution program state values suffix base pc running input
      (by rw [length]; omega) (by rw [length, physical]; omega)
      (by simpa only [length] using loadBlock)
  have loadedHeap : loaded.heap = channelHeap heap rows roots channels := by
    simpa only [values, physical, channelHeap, ForestInputStored.withValues] using lh
  have zeroHeap : loaded.heap = evaluationHeap heap rows roots channels
      (graph.evalPrefix channels 0 (Nat.zero_le _)) := by
    simpa [evaluationHeap, ForestInputStored.withValues, List.ofFn_zero] using loadedHeap
  have loadedCount : loaded.heap[countAddress]'(by rw [lh]; simp; omega) =
      word width graph.nodeCount := by
    simpa only [lh, Array.getElem_append_left countAddressBound] using stored
  obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, fh, fs, fo, fp, fr⟩ :=
    execution program loaded heap graph rows roots matched heads channels (base + 2 * n)
      countAddress zeroHeap countAddressFits (by rw [lh]; simp; omega) loadedCount
      (by simpa only [length] using lp) lr fits room evalBlock
  have loadedLive : loaded.liveWords = state.liveWords := by
    simp [State.liveWords, lh, ls, lo, input, values]
    omega
  refine ⟨final, 2 * values.length + restTicks, max state.liveWords restPeak,
    loadTrace.append restTrace, ?_, ?_, fh, fs.trans ls, fo.trans lo, fp, fr⟩
  · rw [weights_sum] at restTime
    rw [length]
    omega
  · rw [loadedLive] at restSpace
    simp only [max_le_iff]
    exact ⟨by omega, restSpace⟩


/-- Five loaded metadata words precede the shared cache. -/
def packetHeaderHeap (width channels : ℕ) (rows : List Row) (roots : List ℕ) : Array (Word width) :=
  ((globalHeader channels rows roots).map (word width)).toArray

@[simp] theorem packetHeaderHeap_size (width channels : ℕ) (rows : List Row) (roots : List ℕ) :
    (packetHeaderHeap width channels rows roots).size = 5 := by
  simp [packetHeaderHeap]

theorem input_packet_cache (channels : ℕ) (rows : List Row) (roots : List ℕ) :
    ((inputPacket channels 0 rows roots).map (word width)).toArray =
      cacheHeap width (packetHeaderHeap width channels rows roots) rows roots := by
  simp [inputPacket, cacheHeap, Controller.Cost.ForestCursorMaterialize.allocatedHeap,
    packetHeaderHeap, List.map_append, List.append_toArray]

theorem packet_node_count (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) :
    (cacheHeap width (packetHeaderHeap width n rows roots) rows roots)[1]'(by simp; omega) =
      word width graph.nodeCount := by
  have bounded : 1 < (packetHeaderHeap width n rows roots).size := by simp
  change (packetHeaderHeap width n rows roots ++
    ((serializedRows 5 rows roots).map (word width)).toArray)[1] = _
  rw [Array.getElem_append_left bounded]
  simp [packetHeaderHeap, globalHeader, countSource_value, matched.length_eq]

/-- The actual cold source loader, channel loader and shared interpreter run
in one containing program, with no free loaded cache or register reset. -/
theorem cold_execution (program : Program width 4) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (matched : RowsMatch graph rows)
    (heads : HeadsMatch graph rows matched) (rootMatches : RootsMatch graph roots)
    (channels : Channel n → Bool) (suffix output : List (Word width))
    (address loaded temporary : Word width) (base : ℕ)
    (fits : base + 33 + 2 * n + 126 < 2 ^ width)
    (room : (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size +
      n + graph.nodeCount ≤ 2 ^ width)
    (sourceBlock : BlockAt program base (ForestInputMetadata.fullCode width base))
    (channelBlock : BlockAt program (base + 33) (InputLoad.code (width := width) n))
    (evalBlock : BlockAt program (base + 33 + 2 * n)
      (UniformDAGLoop.code width (base + 33 + 2 * n) 1
        (UniformDAGTypedNode.layout (packetHeaderHeap width n rows roots) rows roots channels))) :
    ∃ final ticks peak, Execution program
      ((ForestCounter.counterState (#[] : Array (Word width)) base address loaded temporary).frame
        ((inputPacket n 0 rows roots).map (word width) ++
          List.ofFn (fun i => boolWord width (channels i)) ++ suffix) output)
      final ticks peak ∧
      ticks ≤ 27 + 7 * (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences +
          graph.roots.length) + 2 * n + 43 * graph.nodeCount +
        18 * (graph.childIncidences + graph.guardIncidences) + 6 ∧
      peak ≤ 14 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences +
        graph.roots.length) + n + graph.nodeCount + suffix.length + output.length ∧
      final.heap = evaluationHeap (packetHeaderHeap width n rows roots) rows roots channels
        (graph.evalTable channels) ∧ final.stack = suffix ∧ final.output = output ∧
      final.pc = word width (base + 33 + 2 * n + 126) ∧ final.halted = false := by
  let values := List.ofFn (fun i : Channel n => boolWord width (channels i))
  have length : values.length = n := by simp [values]
  have packetSize : (inputPacket n 0 rows roots).length =
      (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size := by
    have eq := input_packet_cache (width := width) n rows roots
    have sz := congrArg Array.size eq
    simpa using sz
  obtain ⟨cached, sourceTrace, ch, cs, co, cp, cr⟩ :=
    cold_input_packet_execution program base graph rows roots matched rootMatches
      (values ++ suffix) output address loaded temporary (by omega)
      (by rw [packetSize]; omega) sourceBlock
  have physical : cached.heap = cacheHeap width (packetHeaderHeap width n rows roots) rows roots :=
    ch.trans (input_packet_cache n rows roots)
  have countBound : 1 < cached.heap.size := by rw [physical]; simp; omega
  have countWord : cached.heap[1]'countBound = word width graph.nodeCount := by
    simpa only [physical] using packet_node_count (width := width) graph rows roots matched
  obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, fh, fs, fo, fp, fr⟩ :=
    channels_execution program cached (packetHeaderHeap width n rows roots) graph rows roots matched
      heads channels suffix (base + 33) 1 physical cs (by omega) countBound countWord cp cr fits
      room channelBlock evalBlock
  have cachedLive : cached.liveWords =
      10 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences + graph.roots.length) +
        n + suffix.length + output.length := by
    rw [State.liveWords, physical, cs, co]
    simp only [cacheHeap_size, packetHeaderHeap_size, List.length_append, length]
    obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
    have rootsLength : roots.length = graph.roots.length := by rw [rootMatches]; simp
    rw [matched.length_eq, children, guards, rootsLength]
    omega
  refine ⟨final, (27 + 7 * (6 * graph.nodeCount + graph.childIncidences +
    graph.guardIncidences + graph.roots.length)) + restTicks,
    max (10 + (6 * graph.nodeCount + graph.childIncidences + graph.guardIncidences +
      graph.roots.length) + (values ++ suffix).length + output.length) restPeak,
    ?_, ?_, ?_, fh, fs, fo.trans co, fp, fr⟩
  · simpa only [values, List.append_assoc] using sourceTrace.append restTrace
  · omega
  · rw [cachedLive] at restSpace
    simp only [max_le_iff]
    constructor
    · simp only [List.length_append, length]; omega
    · omega

end Controller.Cost.UniformDAGRun
