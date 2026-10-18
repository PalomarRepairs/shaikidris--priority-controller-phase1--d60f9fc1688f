module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.GateProgram

@[expose] public section

/-! Generated topological decoder programs and their represented heap prefixes.
Input loading, sparse initialization and compilation costs are separate refinements. -/
namespace Controller.Cost.DAGProgram

open Controller.Decoder Controller.Cost.GateProgram

/-- Every input coordinate remains stored in the initial heap segment. -/
structure ChannelsStored (assignment : Assignment n) (heap : Array (Word width)) : Prop where
  valid : ∀ label : Channel n, label.val < heap.size
  value : ∀ label : Channel n, heap[label.val]'(valid label) = boolWord width (assignment label)

theorem ChannelsStored.push (assignment : Assignment n) (heap : Array (Word width))
    (stored : ChannelsStored assignment heap) (value : Bool) :
    ChannelsStored assignment (heap.push (boolWord width value)) := by
  refine ⟨?_, ?_⟩
  · intro label; simp only [Array.size_push]; have := stored.valid label; omega
  · intro label
    rw [Array.getElem_push_lt (stored.valid label)]
    exact stored.value label

/-- Generated code for a stored topological prefix, with absolute jump targets. -/
def prefixCode (graph : DAG n) (width base : Nat) :
    (length : Nat) → length ≤ graph.nodeCount → Code width
  | 0, _ => []
  | length + 1, bound =>
    let earlier := prefixCode graph width base length (by omega)
    earlier ++ gateCode width (base + earlier.length)
      (graph.node ⟨length, by omega⟩)

/-- Input coordinates and all computed earlier nodes inhabit one real heap. -/
structure PrefixStored (graph : DAG n) (assignment : Assignment n)
    (length : Nat) (bound : length ≤ graph.nodeCount) (heap : Array (Word width)) : Prop where
  channels : ChannelsStored assignment heap
  table : BoolTableStored (graph.evalVectorPrefix assignment length bound) n heap
  size : heap.size = n + length

theorem PrefixStored.gateValues (graph : DAG n) (assignment : Assignment n)
    (length : Nat) (bound : length + 1 ≤ graph.nodeCount) (heap : Array (Word width))
    (stored : PrefixStored graph assignment length (by omega) heap) :
    GateValuesStored heap (graph.node ⟨length, by omega⟩) assignment
      (fun child => (graph.evalVectorPrefix assignment length (by omega))[child.val]) := by
  refine ⟨?_, ?_⟩
  · intro label _; exact ⟨stored.channels.valid label, stored.channels.value label⟩
  · intro ref _
    have valid : n + ref.val < heap.size := by
      have refBound : ref.val < length := ref.isLt
      rw [stored.size]; omega
    exact ⟨valid, stored.table.entry ref⟩

theorem PrefixStored.push (graph : DAG n) (assignment : Assignment n)
    (length : Nat) (bound : length + 1 ≤ graph.nodeCount) (heap : Array (Word width))
    (stored : PrefixStored graph assignment length (by omega) heap) :
    PrefixStored graph assignment (length + 1) bound
      (heap.push (boolWord width ((graph.node ⟨length, by omega⟩).eval assignment
        (fun child => (graph.evalVectorPrefix assignment length (by omega))[child.val])))) := by
  refine ⟨stored.channels.push _ _ _, ?_, ?_⟩
  · simp only [DAG.evalVectorPrefix]
    exact stored.table.push _ _ _ stored.size.symm _
  · simp only [Array.size_push, stored.size]; omega

/-- A generated prefix is a sub-block of its one-node extension. -/
theorem prefixBlock (graph : DAG n) (program : Program width 4) (base length : Nat)
    (bound : length + 1 ≤ graph.nodeCount)
    (block : BlockAt program base (prefixCode graph width base (length + 1) bound)) :
    BlockAt program base (prefixCode graph width base length (by omega)) := by
  exact BlockAt.prefix _ _ _ _ block

/-- The newly generated gate is fetched after the preceding generated prefix. -/
theorem nextBlock (graph : DAG n) (program : Program width 4) (base length : Nat)
    (bound : length + 1 ≤ graph.nodeCount)
    (block : BlockAt program base (prefixCode graph width base (length + 1) bound)) :
    BlockAt program (base + (prefixCode graph width base length (by omega)).length)
      (gateCode width (base + (prefixCode graph width base length (by omega)).length)
        (graph.node ⟨length, by omega⟩)) := by
  exact BlockAt.suffix _ _ _ _ block

/-- Empty computed table at a represented input heap. -/
theorem initialPrefix (graph : DAG n) (assignment : Assignment n)
    (heap : Array (Word width)) (channels : ChannelsStored assignment heap)
    (size : heap.size = n) : PrefixStored graph assignment 0 (Nat.zero_le _) heap := by
  refine ⟨channels, ⟨?_, ?_⟩, by simpa⟩
  · simp [size]
  · intro index; exact Fin.elim0 index

/-- Incidence work of a topological prefix, including every stored node. -/
def prefixWork (graph : DAG n) : (length : Nat) → length ≤ graph.nodeCount → Nat
  | 0, _ => 0
  | length + 1, bound =>
    prefixWork graph length (by omega) + 1 +
      (graph.node ⟨length, by omega⟩).children.length +
      (graph.node ⟨length, by omega⟩).guardLabels.length

theorem prefixCode_length_le (graph : DAG n) (width base : Nat) :
    ∀ length bound, (prefixCode graph width base length bound).length ≤
      12 * prefixWork graph length bound := by
  intro length
  induction length with
  | zero => intro bound; simp [prefixCode, prefixWork]
  | succ length inductionHypothesis =>
    intro bound
    have earlier := inductionHypothesis (by omega)
    have gateBound := gateCode_length_le width
      (base + (prefixCode graph width base length (by omega)).length)
      (graph.node ⟨length, by omega⟩)
    simp only [prefixCode, List.length_append, prefixWork]
    omega

/-- Prefix work agrees with the multiplicity-retaining stored incidence sums. -/
theorem prefixWork_eq (graph : DAG n) : ∀ length (bound : length ≤ graph.nodeCount),
    prefixWork graph length bound = length +
      (List.ofFn fun index : Fin length => (graph.node (index.castLE bound)).children.length).sum +
      (List.ofFn fun index : Fin length => (graph.node (index.castLE bound)).guardLabels.length).sum := by
  intro length
  induction length with
  | zero => intro bound; simp [prefixWork]
  | succ length inductionHypothesis =>
    intro bound
    rw [prefixWork, inductionHypothesis]
    simp only [List.ofFn_succ', List.sum_concat, Fin.val_last, Fin.castLE, Fin.castSucc, Fin.castAdd]
    omega

/-- The generated decoder code has linear incidence-sensitive stored size. -/
theorem fullCode_length_le (graph : DAG n) (width base : Nat) :
    (prefixCode graph width base graph.nodeCount (Nat.le_refl _)).length ≤
      12 * graph.countedSize := by
  have bound := prefixCode_length_le graph width base graph.nodeCount (Nat.le_refl _)
  rw [prefixWork_eq] at bound
  have localBound : (prefixCode graph width base graph.nodeCount (Nat.le_refl _)).length ≤
      12 * (graph.nodeCount + graph.childIncidences + graph.guardIncidences) := by
    simpa only [Fin.castLE, DAG.childIncidences, DAG.guardIncidences] using bound
  rw [DAG.countedSize_eq]
  omega

/-- Actual execution of every generated topological prefix. Earlier node values
are reused from the same heap, while each represented incidence remains charged. -/
theorem prefix_execution (graph : DAG n) (guarded : graph.Guarded)
    (program : Program width 4) (base : Nat) (assignment : Assignment n)
    (initialHeap : Array (Word width)) (initialAddress initialLoaded : Word width)
    (initialAccumulator : Bool)
    (initial : PrefixStored graph assignment 0 (Nat.zero_le _) initialHeap) :
    ∀ (length : Nat) (bound : length ≤ graph.nodeCount),
      base + (prefixCode graph width base length bound).length < 2 ^ width →
      n + length < 2 ^ width →
      BlockAt program base (prefixCode graph width base length bound) →
      ∃ heap finalAddress finalLoaded finalAccumulator ticks,
        PrefixStored graph assignment length bound heap ∧
        Execution program (cellState initialHeap base initialAddress initialLoaded initialAccumulator)
          (cellState heap (base + (prefixCode graph width base length bound).length)
            finalAddress finalLoaded finalAccumulator) ticks (5 + heap.size) ∧
        ticks ≤ (prefixCode graph width base length bound).length := by
  intro length
  induction length with
  | zero =>
    intro bound programFits heapFits block
    refine ⟨initialHeap, initialAddress, initialLoaded, initialAccumulator, 0, initial, ?_, ?_⟩
    · simpa [prefixCode] using Execution.refl
        (cellState initialHeap base initialAddress initialLoaded initialAccumulator)
    · simp [prefixCode]
  | succ length inductionHypothesis =>
    intro bound programFits heapFits block
    have earlierBound : length ≤ graph.nodeCount := by omega
    have shorter : (prefixCode graph width base length earlierBound).length ≤
        (prefixCode graph width base (length + 1) bound).length := by
      simp only [prefixCode, List.length_append]; omega
    obtain ⟨heap, address, loaded, accumulator, ticks, stored, earlierTrace, tickBound⟩ :=
      inductionHypothesis earlierBound (by omega) (by omega)
        (prefixBlock graph program base length bound block)
    have values := stored.gateValues graph assignment length bound heap
    have gateFits : base + (prefixCode graph width base length earlierBound).length +
        (gateCode width (base + (prefixCode graph width base length earlierBound).length)
          (graph.node ⟨length, by omega⟩)).length < 2 ^ width := by
      simpa only [prefixCode, List.length_append, Nat.add_assoc] using programFits
    obtain ⟨finalAddress, finalLoaded, gateTicks, gateTrace, gateTickBound⟩ :=
      guarded_gate_execution program heap
        (base + (prefixCode graph width base length earlierBound).length)
        (graph.node ⟨length, by omega⟩) (guarded _) assignment
        (fun child => (graph.evalVectorPrefix assignment length earlierBound)[child.val])
        address loaded accumulator gateFits (by rw [stored.size]; omega) values
        (nextBlock graph program base length bound block)
    refine ⟨_, finalAddress, finalLoaded,
      (graph.node ⟨length, by omega⟩).eval assignment
        (fun child => (graph.evalVectorPrefix assignment length earlierBound)[child.val]),
      ticks + gateTicks, stored.push graph assignment length bound heap, ?_, ?_⟩
    · have trace := earlierTrace.append gateTrace
      have peak : max (5 + heap.size) (6 + heap.size) =
          5 + (heap.push (boolWord width ((graph.node ⟨length, by omega⟩).eval assignment
            (fun child => (graph.evalVectorPrefix assignment length earlierBound)[child.val])))).size := by
        simp only [Array.size_push]; omega
      simpa only [prefixCode, List.length_append, Nat.add_assoc, peak] using trace
    · simpa only [prefixCode, List.length_append] using Nat.add_le_add tickBound gateTickBound

/-- Whole decoder kernel: every stored node is evaluated once and the final
heap table agrees with semantic evaluation, including shared and unused nodes. -/
theorem full_execution (graph : DAG n) (guarded : graph.Guarded)
    (program : Program width 4) (base : Nat) (assignment : Assignment n)
    (initialHeap : Array (Word width)) (initialAddress initialLoaded : Word width)
    (initialAccumulator : Bool) (inputs : ChannelsStored assignment initialHeap)
    (initialSize : initialHeap.size = n)
    (programFits : base + (prefixCode graph width base graph.nodeCount (Nat.le_refl _)).length < 2 ^ width)
    (heapFits : n + graph.nodeCount < 2 ^ width)
    (block : BlockAt program base (prefixCode graph width base graph.nodeCount (Nat.le_refl _))) :
    ∃ heap finalAddress finalLoaded finalAccumulator ticks,
      ChannelsStored assignment heap ∧ heap.size = n + graph.nodeCount ∧
      (∀ index : Fin graph.nodeCount,
        ∃ valid : n + index.val < heap.size,
          heap[n + index.val] = boolWord width (graph.eval assignment index)) ∧
      Execution program (cellState initialHeap base initialAddress initialLoaded initialAccumulator)
        (cellState heap (base + (prefixCode graph width base graph.nodeCount (Nat.le_refl _)).length)
          finalAddress finalLoaded finalAccumulator) ticks (5 + n + graph.nodeCount) ∧
      ticks ≤ 12 * graph.countedSize := by
  obtain ⟨heap, address, loaded, accumulator, ticks, stored, trace, tickBound⟩ :=
    prefix_execution graph guarded program base assignment initialHeap initialAddress initialLoaded
      initialAccumulator (initialPrefix graph assignment initialHeap inputs initialSize)
      graph.nodeCount (Nat.le_refl _) programFits heapFits block
  refine ⟨heap, address, loaded, accumulator, ticks, stored.channels, stored.size, ?_, ?_,
    tickBound.trans (fullCode_length_le graph width base)⟩
  · intro index
    have valid : n + index.val < heap.size := by rw [stored.size]; have := index.isLt; omega
    refine ⟨valid, ?_⟩
    rw [stored.table.entry index, graph.evalVectorPrefix_eq_eval]
    rfl
  · simpa only [stored.size, Nat.add_assoc] using trace

def generatedProgram (graph : DAG n) (width : Nat) : Program width 4 :=
  (prefixCode graph width 0 graph.nodeCount (Nat.le_refl _)).toArray.push .halt

theorem generatedProgram_block (graph : DAG n) (width : Nat) :
    BlockAt (generatedProgram graph width) 0
      (prefixCode graph width 0 graph.nodeCount (Nat.le_refl _)) := by
  intro offset bound
  have notEnd : offset ≠ (prefixCode graph width 0 graph.nodeCount (Nat.le_refl _)).length := by omega
  simp only [generatedProgram, Nat.zero_add, Array.getElem?_push, List.size_toArray,
    notEnd, ite_false, List.getElem?_toArray]

theorem generatedProgram_size_le (graph : DAG n) (width : Nat) :
    (generatedProgram graph width).size ≤ 12 * graph.countedSize + 1 := by
  simp only [generatedProgram, Array.size_push, List.size_toArray]
  have bound := fullCode_length_le graph width 0
  omega

/-- Resident kernel space includes all stored instructions and the input/node heap. -/
theorem generatedProgram_peak_resident_le (graph : DAG n) (width : Nat) :
    programWords (generatedProgram graph width) + (5 + n + graph.nodeCount) ≤
      49 * graph.countedSize + 9 := by
  have programBound := generatedProgram_size_le graph width
  have tableBound : n + graph.nodeCount ≤ graph.countedSize := by
    rw [DAG.countedSize_eq]; omega
  unfold programWords
  omega

/-- The corresponding bit-space bound retains its word-width factor. -/
theorem generatedProgram_peak_bits_le (graph : DAG n) (width : Nat) :
    width * (programWords (generatedProgram graph width) + (5 + n + graph.nodeCount)) ≤
      width * (49 * graph.countedSize + 9) :=
  Nat.mul_le_mul_left width (generatedProgram_peak_resident_le graph width)

end Controller.Cost.DAGProgram
