module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralSource

@[expose] public section

/-! A fixed interpreter computes one complete literal-propagation column from
the original packet. The node count, tags, and operand identities are fetched;
all loop frames are pushed and popped by the executed program. -/
namespace Controller.Extensions.LiteralSourceRun
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputPrefixStored
open Controller.Cost.UniformDAGSource Controller.Cost.ForestInputStored
open Controller.Cost.UniformDAGRun (packetHeaderHeap packetHeaderHeap_size packet_node_count)
open Controller.Extensions.LiteralSource

variable (config : LiteralSourceNode.Mode)

def evalPrefix (graph : DAG n) (channels : Assignment n) :
    (length : Nat) → length ≤ graph.nodeCount → Fin length → Bool
  | 0, _ => Fin.elim0
  | length + 1, bound =>
    let earlier := evalPrefix graph channels length (Nat.le_trans (Nat.le_succ length) bound)
    let gate := graph.node ⟨length, Nat.lt_of_lt_of_le (Nat.lt_succ_self length) bound⟩
    Fin.lastCases (gateValue config gate channels earlier) earlier

def evalTable (graph : DAG n) (channels : Assignment n) : Fin graph.nodeCount → Bool :=
  evalPrefix config graph channels graph.nodeCount (Nat.le_refl _)

def code (width base countAddress : Nat) (layout : UniformDAGNode.Layout) : Code width :=
  UniformDAGLoop.initializeCode width countAddress ++
    (UniformDAGLoop.enterCode width (base + 117) ++
      (LiteralSourceNode.code width (base + 8) layout config ++ UniformDAGLoop.advanceCode width (base + 4)))

@[simp] theorem code_length (width base countAddress : Nat) (layout : UniformDAGNode.Layout) :
    (code config width base countAddress layout).length = 117 := by simp [code]

theorem node_block (program : Program width 4) (base countAddress : Nat)
    (layout : UniformDAGNode.Layout)
    (block : BlockAt program base (code config width base countAddress layout)) :
    BlockAt program (base + 8) (LiteralSourceNode.code width (base + 8) layout config) := by
  have b1 := BlockAt.suffix program base _ _ block
  have b2 := BlockAt.suffix program _ _ _ b1
  simpa only [UniformDAGLoop.initializeCode_length, UniformDAGLoop.enterCode_length, Nat.add_assoc] using
    BlockAt.prefix program _ _ _ b2

private theorem blocks (program : Program width 4) (base countAddress : ℕ)
    (layout : UniformDAGNode.Layout)
    (block : BlockAt program base (code config width base countAddress layout)) :
    BlockAt program (base + 4) (UniformDAGLoop.enterCode width (base + 117)) ∧
    BlockAt program (base + 108) (UniformDAGLoop.advanceCode width (base + 4)) := by
  have afterInit := BlockAt.suffix program base (UniformDAGLoop.initializeCode width countAddress)
    (UniformDAGLoop.enterCode width (base + 117) ++
      (LiteralSourceNode.code width (base + 8) layout config ++ UniformDAGLoop.advanceCode width (base + 4))) block
  have entered : BlockAt program (base + 4)
      (UniformDAGLoop.enterCode width (base + 117) ++
        (LiteralSourceNode.code width (base + 8) layout config ++ UniformDAGLoop.advanceCode width (base + 4))) := by
    simpa only [UniformDAGLoop.initializeCode_length] using afterInit
  have enterBlock := BlockAt.prefix program (base + 4) (UniformDAGLoop.enterCode width (base + 117))
    (LiteralSourceNode.code width (base + 8) layout config ++ UniformDAGLoop.advanceCode width (base + 4)) entered
  have afterEnter : BlockAt program (base + 8)
      (LiteralSourceNode.code width (base + 8) layout config ++ UniformDAGLoop.advanceCode width (base + 4)) := by
    simpa only [UniformDAGLoop.enterCode_length, Nat.add_assoc] using
      BlockAt.suffix program (base + 4) (UniformDAGLoop.enterCode width (base + 117)) _ entered
  have tail := BlockAt.suffix program (base + 8) (LiteralSourceNode.code width (base + 8) layout config)
    (UniformDAGLoop.advanceCode width (base + 4)) afterEnter
  exact ⟨enterBlock, by simpa only [LiteralSourceNode.code_length, Nat.add_assoc] using tail⟩

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
    (running : state.halted = false) (fits : base + 117 < 2 ^ width)
    (room : state.heap.size < 2 ^ width)
    (block : BlockAt program base
      (code config width base countAddress (UniformDAGTypedNode.layout heap rows roots channels))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 45 + 18 * ((graph.node node).children.length + (graph.node node).guardLabels.length) ∧
      peak ≤ state.liveWords + 3 ∧
      final.heap = state.heap.push (boolWord width (gateValue config (graph.node node) channels earlier)) ∧
      final.stack = word width (remaining - 1) :: suffix ∧ final.output = state.output ∧
      final.reg 3 = word width (2 * (node.val + 1)) ∧
      final.pc = word width (base + 4) ∧ final.halted = false := by
  obtain ⟨enterBlock, tailBlock⟩ := blocks config program base countAddress _ block
  obtain ⟨ready, entryPeak, et, ep, eh, eo, es, er3, ePC, er⟩ :=
    UniformDAGLoop.enter_execution program state (base + 4) (base + 117) remaining suffix
      positive countFits stack pc running (by omega) enterBlock
  have entryLive : ready.liveWords = state.liveWords + 1 := by
    simp [State.liveWords, eh, eo, es, stack]; omega
  obtain ⟨allocated, nodeTicks, nodePeak, nt, np, ns, nh, nst, no, nPC, nr⟩ :=
    LiteralSource.node_execution program ready heap graph rows roots matched heads node channels earlier
      config (eh.trans physical) (er3.trans offset) (base + 8)
      (by simpa only [Nat.add_assoc] using ePC) er (by omega)
      (by simpa only [eh] using room) (node_block config program base countAddress _ block)
  have offsetFits : 2 * node.val + 2 < 2 ^ width := by
    have rowBound : node.val < rows.length := by rw [matched.length_eq]; exact node.isLt
    rw [physical, evaluationHeap_size, cacheHeap_size] at room
    omega
  obtain ⟨final, tailPeak, atTrace, ap, ah, ao, ast, ar3, aPC, ar⟩ :=
    UniformDAGLoop.advance_execution program allocated (base + 108) (base + 4)
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


def weights (graph : DAG n) : List ℕ :=
  List.ofFn (fun index : Fin graph.nodeCount =>
    45 + 18 * ((graph.node index).children.length + (graph.node index).guardLabels.length))

@[simp] theorem weights_length (graph : DAG n) : (weights graph).length = graph.nodeCount := by
  simp [weights]


/-- Every stored child and guard occurrence contributes its actual scan cost. -/
theorem weights_sum (graph : DAG n) :
    (weights graph).sum = 45 * graph.nodeCount +
      18 * (graph.childIncidences + graph.guardIncidences) := by
  simp only [weights, DAG.childIncidences, DAG.guardIncidences, List.sum_ofFn]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

private theorem extended_heap (heap : Array (Word width)) (graph : DAG n)
    (rows : List Row) (roots : List ℕ) (channels : Channel n → Bool)
    (k : ℕ) (bound : k ≤ graph.nodeCount) (nextBound : k + 1 ≤ graph.nodeCount) :
    evaluationHeap heap rows roots channels (evalPrefix config graph channels (k + 1) nextBound) =
      (evaluationHeap heap rows roots channels (evalPrefix config graph channels k bound)).push
        (boolWord width (gateValue config (graph.node ⟨k, by omega⟩) channels (evalPrefix config graph channels k bound))) := by
  simpa only [evaluationHeap, evalPrefix] using
    append_value (channelHeap heap rows roots channels) (evalPrefix config graph channels k bound)
      (gateValue config (graph.node ⟨k, by omega⟩) channels (evalPrefix config graph channels k bound))

/-- The whole remaining decoder suffix follows actual loop backedges and
allocates its complete topological table. No node is skipped or revisited. -/
theorem suffix_execution (program : Program width 4)
    (heap : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List ℕ)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (channels : Channel n → Bool) (base countAddress : ℕ)
    (fits : base + 117 < 2 ^ width)
    (room : (cacheHeap width heap rows roots).size + n + graph.nodeCount ≤ 2 ^ width)
    (block : BlockAt program base
      (code config width base countAddress (UniformDAGTypedNode.layout heap rows roots channels))) :
    ∀ remaining k, (total : k + remaining = graph.nodeCount) →
      (bound : k ≤ graph.nodeCount) → (state : State width 4) →
      state.heap = evaluationHeap heap rows roots channels (evalPrefix config graph channels k bound) →
      state.reg 3 = word width (2 * k) →
      (suffix : List (Word width)) → state.stack = word width remaining :: suffix →
      state.pc = word width (base + 4) → state.halted = false →
      ∃ final ticks peak, Execution program state final ticks peak ∧
        ticks ≤ ((weights graph).drop k).sum + 2 ∧ peak ≤ state.liveWords + remaining + 3 ∧
        final.heap = evaluationHeap heap rows roots channels (evalTable config graph channels) ∧
        final.stack = suffix ∧ final.output = state.output ∧
        final.pc = word width (base + 117) ∧ final.halted = false := by
  intro remaining
  induction remaining with
  | zero =>
      intro k total bound state physical offset suffix stack pc running
      have atEnd : k = graph.nodeCount := by omega
      subst k
      obtain ⟨enterBlock, tailBlock⟩ := blocks config program base countAddress _ block
      obtain ⟨final, peak, trace, space, fh, fo, fs, fp, fr⟩ :=
        UniformDAGLoop.exit_execution program state (base + 4) (base + 117) suffix
          stack pc running (by omega) enterBlock
      refine ⟨final, 2, peak, trace, ?_, by omega, ?_, fs, fo, fp, fr⟩
      · have empty : (weights graph).drop graph.nodeCount = [] := by
          simpa only [weights_length] using (List.drop_length (l := weights graph))
        simp only [empty, List.sum_nil, Nat.zero_add, le_refl]
      · simpa only [evalTable] using fh.trans physical
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
        iteration config program state heap graph rows roots matched heads node channels
          (evalPrefix config graph channels k bound) physical offset (remaining + 1) (by omega) countFits
          suffix stack base countAddress pc running fits stateRoom block
      have nextPhysical : next.heap =
          evaluationHeap heap rows roots channels (evalPrefix config graph channels (k + 1) nextBound) := by
        rw [extended_heap config heap graph rows roots channels k bound nextBound]
        simpa only [node, physical] using nh
      obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, fh, fs, fo, fp, fr⟩ :=
        ih (k + 1) (by omega) nextBound next nextPhysical nr3 suffix
          (by simpa only [Nat.add_sub_cancel] using ns) np nr
      have nextLive : next.liveWords = state.liveWords + 1 := by
        simp [State.liveWords, nh, ns, no, stack]; omega
      have validWeight : k < (weights graph).length := by simpa only [weights_length] using valid
      have split := List.drop_eq_getElem_cons validWeight
      have weight : (weights graph)[k]'validWeight =
          45 + 18 * ((graph.node node).children.length + (graph.node node).guardLabels.length) := by
        simp only [weights, List.getElem_ofFn, node]
      have sumSplit : ((weights graph).drop k).sum =
          45 + 18 * ((graph.node node).children.length + (graph.node node).guardLabels.length) +
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
      (evalPrefix config graph channels 0 (Nat.zero_le _)))
    (countAddressFits : countAddress < 2 ^ width)
    (countAddressBound : countAddress < state.heap.size)
    (stored : state.heap[countAddress] = word width graph.nodeCount)
    (pc : state.pc = word width base) (running : state.halted = false)
    (fits : base + 117 < 2 ^ width)
    (room : (cacheHeap width heap rows roots).size + n + graph.nodeCount ≤ 2 ^ width)
    (block : BlockAt program base
      (code config width base countAddress (UniformDAGTypedNode.layout heap rows roots channels))) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ (weights graph).sum + 6 ∧ peak ≤ state.liveWords + graph.nodeCount + 4 ∧
      final.heap = evaluationHeap heap rows roots channels (evalTable config graph channels) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (base + 117) ∧ final.halted = false := by
  have initialBlock := BlockAt.prefix program base (UniformDAGLoop.initializeCode width countAddress)
    (UniformDAGLoop.enterCode width (base + 117) ++
      (LiteralSourceNode.code width (base + 8) (UniformDAGTypedNode.layout heap rows roots channels) config ++
        UniformDAGLoop.advanceCode width (base + 4))) block
  obtain ⟨ready, entryPeak, startTrace, startSpace, rh, ro, rs, rr3, rp, rr⟩ :=
    UniformDAGRun.initialize_execution program state base countAddress graph.nodeCount countAddressFits
      countAddressBound stored pc running (by omega) initialBlock
  obtain ⟨final, restTicks, restPeak, restTrace, restTime, restSpace, fh, fs, fo, fp, fr⟩ :=
    suffix_execution config program heap graph rows roots matched heads channels base countAddress fits room
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

theorem prefix_flags (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (probe : Fin (n + 1)) (lane : Fin 3) :
    ∀ (length : Nat) (bound : length ≤ graph.nodeCount) (index : Fin length),
      evalPrefix (mode probe lane) graph (fun c => decide (c.castSucc = probe)) length bound index =
        LiteralMachine.flags (LiteralMachine.summary graph (index.castLE bound)) probe lane := by
  intro length
  induction length with
  | zero => intro bound index; exact Fin.elim0 index
  | succ length ih =>
    intro bound index
    refine Fin.lastCases ?_ (fun previous => ?_) index
    · simp only [evalPrefix, Fin.lastCases_last]
      rw [LiteralMachine.summary]
      have allowed : ∀ children, graph.node ((Fin.last length).castLE bound) = .disj children →
          children.length ≤ 1 := by
        intro children gate
        simpa only [gate] using noOr ((Fin.last length).castLE bound)
      rw [← gate_flags _ allowed _ probe lane]
      congr 1
      funext child
      exact ih _ child
    · simp only [evalPrefix, Fin.lastCases_castSucc]
      simpa only [Fin.castLE, Fin.castSucc, Fin.castAdd] using
        ih (Nat.le_trans (Nat.le_succ length) bound) previous

theorem table_flags (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (probe : Fin (n + 1)) (lane : Fin 3) (node : Fin graph.nodeCount) :
    evalTable (mode probe lane) graph (fun c => decide (c.castSucc = probe)) node =
      LiteralMachine.flags (LiteralMachine.summary graph node) probe lane :=
  prefix_flags graph noOr probe lane graph.nodeCount (Nat.le_refl _) node

set_option maxHeartbeats 2000000 in
theorem from_source (resident : Program width 4) (state : State width 4)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n) (entry : Nat)
    (physical : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots values)
    (position : state.pc = word width entry) (running : state.halted = false)
    (fits : entry + 117 < 2 ^ width) (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (storedCode : BlockAt resident entry (code config width entry 1
      (UniformDAGTypedNode.layout (packetHeaderHeap width n rows roots) rows roots values))) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 45 * graph.countedSize + 6 ∧ peak ≤ state.liveWords + graph.nodeCount + 4 ∧
      final.heap = evaluationHeap (packetHeaderHeap width n rows roots) rows roots values (evalTable config graph values) ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 117) ∧ final.halted = false := by
  have size := graph.countedSize_eq
  obtain ⟨children, guards⟩ := matched_incidence_lengths graph rows matched
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have heapBound : (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size + n + graph.nodeCount < 2 ^ width := by
    simp only [cacheHeap_size, packetHeaderHeap_size]
    rw [matched.length_eq, children, guards, rootCount]
    omega
  have firstPrefix : 1 < (cacheHeap width (packetHeaderHeap width n rows roots) rows roots).size := by simp; omega
  have countBound : 1 < state.heap.size := by rw [physical, channelHeap_size]; omega
  have countCell : state.heap[1]'countBound = word width graph.nodeCount := by
    simpa only [physical, channelHeap] using (source_preserved (cacheHeap width (packetHeaderHeap width n rows roots) rows roots) values 1 firstPrefix).trans
      (packet_node_count graph rows roots matched)
  have start : state.heap = evaluationHeap (packetHeaderHeap width n rows roots) rows roots values
      (evalPrefix config graph values 0 (Nat.zero_le _)) := by
    rw [physical]
    simp [evaluationHeap, withValues]
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, output, pc, halted⟩ :=
    execution config resident state (packetHeaderHeap width n rows roots) graph rows roots matched heads
      values entry 1 start (by omega) countBound countCell position running fits (by omega) storedCode
  refine ⟨final, ticks, peak, trace, ?_, space, heap, stack, output, pc, halted⟩
  rw [weights_sum] at time
  omega

end Controller.Extensions.LiteralSourceRun
