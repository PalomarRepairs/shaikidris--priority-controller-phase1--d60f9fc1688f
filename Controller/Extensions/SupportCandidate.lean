module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportSourceRound
public import Controller.Extensions.SupportRootScan
public import Controller.Extensions.SupportTarget
public import Controller.Extensions.BoundedAnd
public import Controller.Cost.UniformDAGRuntimeOutputs

@[expose] public section

/-! A support candidate uses one retained healthy table and one temporary DAG
value table. Each observed root is read from the packet; both outcomes reclaim
the temporary table before returning to their continuation. -/
namespace Controller.Extensions.SupportCandidate
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.ForestInputPrefixStored Controller.Cost.UniformDAGRun
open Controller.Cost.UniformDAGSource Controller.Cost.UniformDAGRuntimeOutputs
open Controller.Cost.SharedDetectorAssembly

def lookup (values : Fin m → Bool) (index : Nat) : Bool :=
  if valid : index < m then values ⟨index, valid⟩ else false

@[simp] theorem lookup_fin (values : Fin m → Bool) (index : Fin m) :
    lookup values index.val = values index := by simp [lookup]

def header (width n : Nat) (rows : List Row) (roots : List Nat) (healthy : Fin m → Bool) :
    Array (Word width) :=
  packetHeaderHeap width n rows roots ++ (List.ofFn (fun i => boolWord width (healthy i))).toArray

@[simp] theorem header_size (roots : List Nat) (healthy : Fin m → Bool) :
    (header width n rows roots healthy).size = 5 + m := by simp [header]

theorem header_count (graph : DAG n) (rows : List Row) (roots : List Nat)
    (healthy : Fin graph.nodeCount → Bool) (matched : RowsMatch graph rows) :
    (header width n rows roots healthy)[1]? = some (word width graph.nodeCount) := by
  unfold header
  rw [Array.getElem?_append_left (by simp)]
  simp [packetHeaderHeap, globalHeader, countSource_value, matched.length_eq]

theorem header_value (roots : List Nat) (healthy : Fin m → Bool) (index : Fin m) :
    (header width n rows roots healthy)[5 + index.val]? = some (boolWord width (healthy index)) := by
  simp [header, index.isLt]

theorem retained_cell (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (values : Assignment n) (nodes : Fin m → Bool) (address : Nat) (valid : address < packet.size) :
    (evaluationHeap packet rows roots values nodes)[address]? = packet[address]? := by
  have bound : address < (cacheHeap width packet rows roots).size := by simp; omega
  have prefixCell := Controller.Cost.ForestCursorMaterialize.allocatedHeap_prefix width packet
    (serializedRows packet.size rows roots) address valid
  unfold evaluationHeap channelHeap withValues
  rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_left bound]
  exact prefixCell

theorem channel_retained_cell (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (values : Assignment n) (address : Nat) (valid : address < packet.size) :
    (channelHeap packet rows roots values)[address]? = packet[address]? := by
  unfold channelHeap withValues
  rw [Array.getElem?_append_left (by simp; omega)]
  exact Controller.Cost.ForestCursorMaterialize.allocatedHeap_prefix width packet
    (serializedRows packet.size rows roots) address valid

def finishCode (width entry destination count : Nat) : List (Instruction width 8) :=
  (SharedEvaluationReclaim.code width entry (entry + 7) count).toList ++
    [.constant 0 (word width 0), .branchZero 0 (word width destination)]

@[simp] theorem finishCode_length : (finishCode width entry destination count).length = 9 := by
  simp [finishCode]

theorem finish_execution (program : Program width 8) (state : State width 8)
    (entry destination : Nat) (retained : Array (Word width)) (nodes : Fin m → Bool)
    (heapStored : state.heap = withValues retained nodes)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 9 < 2 ^ width) (countFits : m < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (finishCode width entry destination m)) :
    ∃ final, Execution program state final (4 * m + 6) state.liveWords ∧
      final.heap = retained ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width destination ∧ final.halted = false := by
  have firstAt := block_left program entry _ _ present
  have lastAt := block_right program entry _ _ present
  simp only [SharedEvaluationReclaim.code_size, Array.length_toList] at lastAt
  obtain ⟨reclaimed, first, heap, stack, output, pc, active, _, _, _, _⟩ :=
    SharedGraphReclaim.setup_execution program state entry (entry + 7) retained
      (List.ofFn (fun i => boolWord width (nodes i))) position running (by omega) heapStored
      (by simpa using countFits) (by simpa using block_code _ _ _ firstAt)
  obtain ⟨final, last, fp, fh, fs, fo, fr, _⟩ :=
    EnumerationSteps.jump_execution program reclaimed (entry + 7) destination pc active (by omega)
      (by simpa using lastAt 0 (by simp)) (by simpa using lastAt 1 (by simp))
  have live : reclaimed.liveWords ≤ state.liveWords := Execution.final_storage_le first
  refine ⟨final, ?_, fh.trans heap, fs.trans stack, fo.trans output, fp, fr⟩
  simpa only [List.length_ofFn, Nat.max_eq_left live, Nat.add_assoc, Nat.reduceAdd] using first.append last

def code (width n : Nat) (packet : Array (Word width)) (rows : List Row) (roots : List Nat)
    (entry healthyBase found rejected : Nat) : List (Instruction width 8) :=
  (SupportSourceRound.code width n packet rows roots entry).toList ++
    (SupportRootScan.code width (entry + 126) (rootBase packet rows) healthyBase
      ((cacheHeap width packet rows roots).size + n) (entry + 126 + 15 * roots.length + 9) roots.length ++
    (finishCode width (entry + 126 + 15 * roots.length) rejected rows.length ++
    finishCode width (entry + 126 + 15 * roots.length + 9) found rows.length))

@[simp] theorem code_length (roots : List Nat) :
    (code width n packet rows roots entry healthyBase found rejected).length = 144 + 15 * roots.length := by
  simp [code]; omega

theorem code_words (roots : List Nat) :
    4 * (code width n packet rows roots entry healthyBase found rejected).length = 576 + 60 * roots.length := by
  rw [code_length]; omega

set_option maxHeartbeats 2000000 in
theorem execution (program : Program width 8) (state : State width 8)
    (packet : Array (Word width)) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (values : Assignment n)
    (healthy : Fin graph.nodeCount → Bool) (entry healthyBase found rejected : Nat)
    (heapStored : state.heap = channelHeap packet rows roots values)
    (countStored : state.heap[1]? = some (word width graph.nodeCount))
    (healthyStored : ∀ root ∈ graph.roots,
      packet[healthyBase + root.val]? = some (boolWord width (healthy root)))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 144 + 15 * roots.length < 2 ^ width)
    (capacity : (cacheHeap width packet rows roots).size + n + graph.nodeCount < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry
      (code width n packet rows roots entry healthyBase found rejected)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ 43 * graph.countedSize + 13 * roots.length + 4 * graph.nodeCount + 12 ∧
      peak ≤ state.liveWords + graph.nodeCount + 4 ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if graph.roots.any (fun root => !healthy root && graph.evalTable values root)
        then found else rejected) ∧ final.halted = false := by
  unfold code at present
  have evalAt := block_left program entry _ _ present
  have afterEval := block_right program entry _ _ present
  simp only [Array.length_toList, SupportSourceRound.code_size] at afterEval
  have scanAt := block_left program (entry + 126) _ _ afterEval
  have afterScan := block_right program (entry + 126) _ _ afterEval
  simp only [SupportRootScan.code_length] at afterScan
  have noAt := block_left program (entry + 126 + 15 * roots.length) _ _ afterScan
  have yesAt := block_right program (entry + 126 + 15 * roots.length) _ _ afterScan
  simp only [finishCode_length] at yesAt
  rw [matched.length_eq] at noAt yesAt
  obtain ⟨evaluated, et, ep, evaluation, etime, espace, eh, es, eo, epos, er, _⟩ :=
    SupportSourceRound.execution program state packet graph rows roots matched heads values entry heapStored
      countStored position running (by omega) capacity (block_code _ _ _ evalAt)
  have rootsEq : roots = graph.roots.map Fin.val := rootMatches
  have source : ∀ i (below : i < roots.length),
      evaluated.heap[rootBase packet rows + i]? = some (word width roots[i]) := by
    intro i below
    have bound : rootBase packet rows + i < (cacheHeap width packet rows roots).size := by
      simp only [rootBase, cacheHeap_size]; omega
    have cell := cache_cell packet rows roots values (graph.evalTable values) _ bound
    have rootCell := cache_root_cell packet rows roots i below
    rw [eh, Array.getElem?_eq_getElem (by simp only [evaluationHeap_size]; omega)]
    exact congrArg some (cell.trans rootCell)
  have healthyCells : ∀ i ∈ roots,
      evaluated.heap[healthyBase + i]? = some (boolWord width (lookup healthy i)) := by
    intro i inRoots
    have inMap : i ∈ graph.roots.map Fin.val := by rw [← rootsEq]; exact inRoots
    obtain ⟨root, inGraph, identifier⟩ := List.mem_map.mp inMap
    subst i
    have cell := healthyStored root inGraph
    have bound := (Array.getElem?_eq_some_iff.mp cell).1
    rw [eh, retained_cell packet rows roots values (graph.evalTable values) _ bound, lookup_fin]
    exact cell
  have valueCells : ∀ i ∈ roots,
      evaluated.heap[(cacheHeap width packet rows roots).size + n + i]? =
        some (boolWord width (lookup (graph.evalTable values) i)) := by
    intro i member
    have inMap : i ∈ graph.roots.map Fin.val := by rw [← rootsEq]; exact member
    obtain ⟨root, _, rfl⟩ := List.mem_map.mp inMap
    have cell := value_cell (channelHeap packet rows roots values) (graph.evalTable values) root
    rw [eh, Array.getElem?_eq_getElem (by simp only [evaluationHeap_size]; omega), lookup_fin]
    simpa only [channelHeap_size, evaluationHeap] using congrArg some cell
  obtain ⟨scanned, st, scan, stime, sh, ss, so, spos, sr⟩ :=
    SupportRootScan.execution program evaluated (entry + 126) (rootBase packet rows) healthyBase
      ((cacheHeap width packet rows roots).size + n) (entry + 126 + 15 * roots.length + 9)
      roots (lookup healthy) (lookup (graph.evalTable values)) source healthyCells valueCells epos er
      (by omega) (by simpa only [eh, evaluationHeap_size] using capacity) scanAt
  have meaning : roots.any (fun i => !lookup healthy i && lookup (graph.evalTable values) i) =
      graph.roots.any (fun root => !healthy root && graph.evalTable values root) := by
    simp [rootsEq, List.any_map, Function.comp_def]
  rw [meaning] at spos
  have evaluatedLive : evaluated.liveWords = state.liveWords + graph.nodeCount := by
    simp only [State.liveWords, eh, es, eo, heapStored, evaluationHeap_size, channelHeap_size]
    omega
  have scannedLive : scanned.liveWords = evaluated.liveWords := by simp only [State.liveWords, sh, ss, so]
  have prefixTrace := evaluation.append scan
  have prefixTime : et + st ≤ 43 * graph.countedSize + 13 * roots.length + 6 := by omega
  have prefixSpace : max ep evaluated.liveWords ≤ state.liveWords + graph.nodeCount + 4 := by omega
  have scannedHeap : scanned.heap = withValues (channelHeap packet rows roots values) (graph.evalTable values) :=
    sh.trans eh
  have finish : ∀ destination offset,
      scanned.pc = word width offset →
      SharedRootRead.BlockAt program offset (finishCode width offset destination graph.nodeCount) →
      offset + 9 < 2 ^ width →
      ∃ final, Execution program scanned final (4 * graph.nodeCount + 6) scanned.liveWords ∧
        final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
        final.pc = word width destination ∧ final.halted = false := by
    intro destination offset atOffset physical fits
    obtain ⟨final, trace, heap, stack, output, pc, active⟩ :=
      finish_execution program scanned offset destination (channelHeap packet rows roots values)
        (graph.evalTable values) scannedHeap atOffset sr fits (by omega) physical
    exact ⟨final, trace, heap.trans heapStored.symm, stack.trans (ss.trans es),
      output.trans (so.trans eo), pc, active⟩
  cases changed : graph.roots.any (fun root => !healthy root && graph.evalTable values root) with
  | false =>
    obtain ⟨final, last, heap, stack, output, pc, active⟩ :=
      finish rejected (entry + 126 + 15 * roots.length) (by simpa [changed] using spos) noAt (by omega)
    refine ⟨final, et + st + (4 * graph.nodeCount + 6), max (max ep evaluated.liveWords) scanned.liveWords,
      prefixTrace.append last, by omega, by omega, heap, stack, output, by simpa [changed] using pc, active⟩
  | true =>
    obtain ⟨final, last, heap, stack, output, pc, active⟩ :=
      finish found (entry + 126 + 15 * roots.length + 9) (by simpa [changed] using spos) yesAt (by omega)
    refine ⟨final, et + st + (4 * graph.nodeCount + 6), max (max ep evaluated.liveWords) scanned.liveWords,
      prefixTrace.append last, by omega, by omega, heap, stack, output, by simpa [changed] using pc, active⟩

theorem supportQuery_isSome (graph : DAG n) (b : Nat) (target : Channel n)
    (healthy : Fin graph.nodeCount → Bool) (chosen : Finset (Channel n)) :
    (BoundedAnd.supportQuery graph b target healthy chosen).isSome =
      graph.roots.any (fun root => !healthy root &&
        graph.evalTable (assignmentOfSet (BoundedAnd.candidate b target chosen)) root) := by
  let candidate := BoundedAnd.candidate b target chosen
  change (if Admissible b target candidate ∧ graph.roots.any (fun root => !healthy root &&
      graph.evalTable (assignmentOfSet candidate) root) then some candidate else none).isSome =
    graph.roots.any (fun root => !healthy root && graph.evalTable (assignmentOfSet candidate) root)
  by_cases changed : graph.roots.any (fun root => !healthy root &&
      graph.evalTable (assignmentOfSet candidate) root) = true
  · obtain ⟨root, _, trueRoot⟩ := List.any_eq_true.mp changed
    have truth : graph.eval (assignmentOfSet candidate) root = true := by
      have pair : healthy root = false ∧ graph.evalTable (assignmentOfSet candidate) root = true := by
        simpa using trueRoot
      simpa only [DAG.evalTable_eq_eval] using pair.2
    have admissible : Admissible b target candidate := by
      refine ⟨graph.nonempty_of_eval_true candidate root truth, ?_⟩
      intro one
      simp [candidate, BoundedAnd.candidate, one]
    simp only [admissible, changed, and_self, ite_true, Option.isSome_some]
  · have unchanged : graph.roots.any (fun root => !healthy root &&
        graph.evalTable (assignmentOfSet candidate) root) = false := by
        cases h : graph.roots.any (fun root => !healthy root &&
          graph.evalTable (assignmentOfSet candidate) root) <;> simp_all
    simp only [unchanged, Bool.false_eq_true, and_false, ite_false, Option.isSome_none]

end Controller.Extensions.SupportCandidate
