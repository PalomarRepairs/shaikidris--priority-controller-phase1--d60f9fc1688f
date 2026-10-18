module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralMachine
public import Controller.Cost.SharedTableBatch
public import Controller.Cost.LiteralConflict

@[expose] public section

/-! A fetched column batch for the literal propagation graph. The entry packet
contains that graph's stored rows and an all-false channel array. The returned
stack has fixed addresses for every sign bit and zero-ancestor bit. -/
namespace Controller.Extensions.LiteralColumns
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.ForestInputPrefixStored Controller.Cost.ForestInputStored Controller.Cost.RawTransferLoops
open Controller.Cost.UniformDAGRun

theorem flatMap_cell (xs : List α) (f : α → List β) (block : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = block) (column : Fin xs.length)
    (offset : Nat) (inside : offset < block) :
    (xs.flatMap f)[column.val * block + offset]? = (f xs[column.val])[offset]? := by
  induction xs with
  | nil => exact Fin.elim0 column
  | cons x rest ih =>
    have headLength := lengths x (by simp)
    refine Fin.cases ?_ (fun j => ?_) column
    · simp only [List.flatMap_cons, Fin.val_zero, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      exact List.getElem?_append_left (by omega)
    ·
      simp only [List.flatMap_cons]
      rw [List.getElem?_append_right (by rw [headLength]; simp only [Fin.val_succ, Nat.succ_mul]; omega)]
      have index : j.succ.val * block + offset - (f x).length = j.val * block + offset := by
        rw [headLength, Fin.val_succ, Nat.succ_mul]; omega
      rw [index]
      simpa only [Fin.val_succ, List.getElem_cons_succ] using
        ih (fun y member => lengths y (by simp [member])) j

def words (original : DAG n) (width : Nat) : List (Word width) :=
  SharedTableBatch.columns (LiteralMachine.graph original) (List.finRange (n + 1)) width

@[simp] theorem words_length (original : DAG n) :
    (words original width).length = (n + 1) * (n + 1 + 3 * original.nodeCount) := by
  simp [words, LiteralMachine.graph]

def address (original : DAG n) (probe : Fin (n + 1)) (root : Fin original.nodeCount) (lane : Fin 3) : Nat :=
  (n - probe.val) * (LiteralMachine.graph original).nodeCount + (LiteralMachine.nodeId original root lane).val

theorem cell (original : DAG n) (probe : Fin (n + 1)) (root : Fin original.nodeCount) (lane : Fin 3) :
    (words original width)[address original probe root lane]? =
      some (boolWord width (LiteralMachine.flags (LiteralMachine.summary original root) probe lane)) := by
  have columnBound : n - probe.val < (List.finRange (n + 1)).reverse.length := by simp
  have selected : (List.finRange (n + 1)).reverse[n - probe.val] = probe := by
    apply Fin.ext
    simp only [List.getElem_reverse, List.length_finRange, List.getElem_finRange]
    change n + 1 - 1 - (n - probe.val) = probe.val
    have := probe.isLt
    omega
  have singletonEq : SharedTableBatch.single probe = LiteralMachine.probeAssignment probe := by
    funext c
    simp [SharedTableBatch.single, SharedCandidateProbe.enabled, LiteralMachine.probeAssignment, eq_comm]
  unfold words SharedTableBatch.columns address
  rw [flatMap_cell _ _ (LiteralMachine.graph original).nodeCount
    (fun _ _ => SharedTableProbe.words_length _ _) ⟨n - probe.val, columnBound⟩
    (LiteralMachine.nodeId original root lane).val (LiteralMachine.nodeId original root lane).isLt]
  rw [selected, singletonEq]
  simp only [SharedTableProbe.words, List.getElem?_ofFn]
  split
  · change some (boolWord width ((LiteralMachine.graph original).evalTable
      (LiteralMachine.probeAssignment probe) (LiteralMachine.nodeId original root lane))) = _
    rw [DAG.evalTable_eq_eval, LiteralMachine.eval_flags]
  · rename_i invalid
    exact (invalid (LiteralMachine.nodeId original root lane).isLt).elim

def read (source : List (Word width)) (index : Nat) : Bool :=
  decide (source[index]? = some (boolWord width true))

theorem read_cell (original : DAG n) (probe : Fin (n + 1)) (root : Fin original.nodeCount) (lane : Fin 3)
    (booleanRoom : 1 < 2 ^ width) :
    read (words original width) (address original probe root lane) =
      LiteralMachine.flags (LiteralMachine.summary original root) probe lane := by
  rw [read, cell]
  cases h : LiteralMachine.flags (LiteralMachine.summary original root) probe lane <;>
    simp [boolWord, word, Nat.mod_eq_of_lt booleanRoom, Nat.mod_eq_of_lt (Nat.two_pow_pos width)]

def decode (original : DAG n) (source : List (Word width)) (root : Fin original.nodeCount) : LiteralMachine.Raw n where
  positive := Finset.univ.filter fun c => read source (address original c.castSucc root 0)
  negative := Finset.univ.filter fun c => read source (address original c.castSucc root 1)
  zero := read source (address original ⟨n, by omega⟩ root 2)

theorem decode_words (original : DAG n) (root : Fin original.nodeCount) (booleanRoom : 1 < 2 ^ width) :
    decode original (words original width) root = LiteralMachine.summary original root := by
  apply LiteralMachine.Raw.ext
  · ext c
    simp [decode, read_cell _ _ _ _ booleanRoom, LiteralMachine.flags]
  · ext c
    simp [decode, read_cell _ _ _ _ booleanRoom, LiteralMachine.flags]
  · simp [decode, read_cell _ _ _ _ booleanRoom, LiteralMachine.flags]

/-- The batch returns the exact literal-summary encoding. Packet construction
from the original DAG and the subsequent contradiction scan are separate runs. -/
theorem execution (resident : Program width 8) (state : State width 8) (original : DAG n)
    (rows : List Row) (roots : List Nat)
    (matched : RowsMatch (LiteralMachine.graph original) rows)
    (heads : HeadsMatch (LiteralMachine.graph original) rows matched)
    (rootMatches : RootsMatch (LiteralMachine.graph original) roots) (entry : Nat)
    (capacity : 4096 * (original.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (SharedTableBatch.code width (n + 1) rows roots entry (List.finRange (n + 1))))
    (room : entry + 152 * (n + 1) < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width (n + 1) rows roots) rows roots (fun _ : Fin (n + 1) => false)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 448 * (n + 1) * (original.countedSize + 1) ∧
      peak ≤ state.liveWords + (n + 2) * (n + 1 + 3 * original.nodeCount) + 4 ∧
      final.heap = state.heap ∧ final.stack = words original width ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 152 * (n + 1)) ∧ final.halted = false ∧
      ∀ root, (decode original (words original width) root).decode = GateBasis.literalSummary original root := by
  have size := LiteralMachine.graph_size original
  have sampleCapacity : 256 * ((LiteralMachine.graph original).countedSize + 1) < 2 ^ width := by omega
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, output, pc, active⟩ :=
    SharedTableBatch.execution resident (LiteralMachine.graph original) rows roots matched heads rootMatches
      (List.finRange (n + 1)) entry state sampleCapacity physical (by simpa using room) position running heapStored
  refine ⟨final, ticks, peak, trace, ?_, ?_, heap, stack, output, by simpa using pc, active, ?_⟩
  · have bound : 53 * (LiteralMachine.graph original).countedSize + 24 ≤ 448 * (original.countedSize + 1) := by omega
    have multiply := Nat.mul_le_mul_left (n + 1) bound
    simp only [List.length_finRange] at time
    simpa only [Nat.mul_assoc, Nat.mul_left_comm] using time.trans multiply
  · simpa only [List.length_finRange, LiteralMachine.graph, Nat.add_assoc] using space
  · intro root
    rw [decode_words _ _ (by omega), LiteralMachine.summary_decode]

theorem address_bound (original : DAG n) (probe : Fin (n + 1)) (root : Fin original.nodeCount) (lane : Fin 3) :
    address original probe root lane < (words original width).length := by
  rw [words_length]
  unfold address
  change (n - probe.val) * (n + 1 + 3 * original.nodeCount) + (LiteralMachine.nodeId original root lane).val < _
  calc
    _ < (n - probe.val) * (n + 1 + 3 * original.nodeCount) + (n + 1 + 3 * original.nodeCount) :=
      Nat.add_lt_add_left (LiteralMachine.nodeId original root lane).isLt _
    _ = (n - probe.val + 1) * (n + 1 + 3 * original.nodeCount) := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

def pairs (original : DAG n) (base : Nat) (root : Fin original.nodeCount) : List (Nat × Nat) :=
  (List.finRange n).map fun c => (base + address original c.castSucc root 0, base + address original c.castSucc root 1)

def jobs (original : DAG n) (base : Nat) : List LiteralConflict.Job :=
  List.ofFn fun root : Fin original.nodeCount =>
    ⟨base + address original ⟨n, by omega⟩ root 2, pairs original base root⟩

def values (width : Nat) (original : DAG n) (base index : Nat) : Bool := read (words original width) (index - base)

theorem collision_pairs (original : DAG n) (base : Nat) (root : Fin original.nodeCount)
    (booleanRoom : 1 < 2 ^ width) :
    LiteralConflict.collision (values width original base) (pairs original base root) =
      (List.finRange n).any (fun c => decide (c ∈ (LiteralMachine.summary original root).positive) &&
        decide (c ∈ (LiteralMachine.summary original root).negative)) := by
  simp [LiteralConflict.collision, pairs, values, read_cell _ _ _ _ booleanRoom, LiteralMachine.flags,
    List.any_map, Function.comp_def]

theorem flags_correct (original : DAG n) (base : Nat) (booleanRoom : 1 < 2 ^ width) :
    LiteralConflict.flags width (values width original base) (jobs original base) =
      List.ofFn (fun root : Fin original.nodeCount => boolWord width (LiteralMachine.summary original root).invalid) := by
  simp only [jobs, LiteralConflict.flags, List.map_ofFn]
  congr 1
  funext root
  change boolWord width (values width original base (base + address original ⟨n, by omega⟩ root 2) ||
    LiteralConflict.collision (values width original base) (pairs original base root)) = _
  rw [collision_pairs _ _ _ booleanRoom]
  simp [values, read_cell _ _ _ _ booleanRoom, LiteralMachine.flags, LiteralMachine.Raw.invalid]

@[simp] theorem jobs_length (original : DAG n) (base : Nat) : (jobs original base).length = original.nodeCount := by simp [jobs]

@[simp] theorem jobs_work (original : DAG n) (base : Nat) :
    LiteralConflict.work (jobs original base) = original.nodeCount * (3 + 9 * n) := by
  simp [LiteralConflict.work, jobs, pairs, List.sum_ofFn]

theorem matrix_cell (original : DAG n) (frame suffix : Array (Word width))
    (probe : Fin (n + 1)) (root : Fin original.nodeCount) (lane : Fin 3) :
    (frame ++ (words original width).toArray ++ suffix)[frame.size + address original probe root lane]? =
      some (boolWord width (LiteralMachine.flags (LiteralMachine.summary original root) probe lane)) := by
  have inside := address_bound original probe root lane (width := width)
  rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
    Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_toArray, cell]

theorem jobs_readable (original : DAG n) (frame suffix : Array (Word width)) :
    ∀ job ∈ jobs original frame.size,
      job.zeroAddress < (frame ++ (words original width).toArray ++ suffix).size ∧
        ∀ pair ∈ job.pairs, pair.1 < (frame ++ (words original width).toArray ++ suffix).size ∧
          pair.2 < (frame ++ (words original width).toArray ++ suffix).size := by
  intro job member
  obtain ⟨root, rfl⟩ := List.mem_ofFn.mp member
  refine ⟨?_, ?_⟩
  · have := address_bound original ⟨n, by omega⟩ root 2 (width := width)
    simp only [Array.size_append, List.size_toArray]
    omega
  · intro pair member
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp member
    have pos := address_bound original c.castSucc root 0 (width := width)
    have neg := address_bound original c.castSucc root 1 (width := width)
    simp only [Array.size_append, List.size_toArray]
    constructor <;> omega

theorem jobs_sources (original : DAG n) (frame suffix : Array (Word width)) (booleanRoom : 1 < 2 ^ width) :
    ∀ job ∈ jobs original frame.size,
      (frame ++ (words original width).toArray ++ suffix)[job.zeroAddress]? =
        some (boolWord width (values width original frame.size job.zeroAddress)) ∧
      ∀ pair ∈ job.pairs,
        (frame ++ (words original width).toArray ++ suffix)[pair.1]? =
          some (boolWord width (values width original frame.size pair.1)) ∧
        (frame ++ (words original width).toArray ++ suffix)[pair.2]? =
          some (boolWord width (values width original frame.size pair.2)) := by
  intro job member
  obtain ⟨root, rfl⟩ := List.mem_ofFn.mp member
  refine ⟨?_, ?_⟩
  · simpa [values, read_cell _ _ _ _ booleanRoom] using matrix_cell original frame suffix ⟨n, by omega⟩ root 2
  · intro pair member
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp member
    constructor
    · simpa [values, read_cell _ _ _ _ booleanRoom] using matrix_cell original frame suffix c.castSucc root 0
    · simpa [values, read_cell _ _ _ _ booleanRoom] using matrix_cell original frame suffix c.castSucc root 1

def constructionCode (original : DAG n) (width : Nat) (rows : List Row) (roots : List Nat)
    (entry sourceSize : Nat) : Program width 8 :=
  SharedTableBatch.code width (n + 1) rows roots entry (List.finRange (n + 1)) ++
    ((SharedWitnessPark.code width ((n + 1) * (n + 1 + 3 * original.nodeCount))).toArray ++
      LiteralConflict.jobsCode width
        (entry + 152 * (n + 1) + 2 * ((n + 1) * (n + 1 + 3 * original.nodeCount)))
        (sourceSize + (n + 1) * (n + 1 + 3 * original.nodeCount)) (jobs original sourceSize))

def constructionSize (original : DAG n) : Nat :=
  152 * (n + 1) + 2 * ((n + 1) * (n + 1 + 3 * original.nodeCount)) + original.nodeCount * (3 + 9 * n)

@[simp] theorem constructionCode_size (original : DAG n) (width : Nat) (rows : List Row) (roots : List Nat)
    (entry sourceSize : Nat) :
    (constructionCode original width rows roots entry sourceSize).size = constructionSize original := by
  simp [constructionCode, constructionSize, Nat.add_assoc]

set_option maxHeartbeats 800000 in
/-- A single fetched run constructs all sign columns and all normalized zero
flags. It starts with the propagation graph's retained input packet. -/
theorem construction_execution (resident : Program width 8) (state : State width 8) (original : DAG n)
    (rows : List Row) (roots : List Nat)
    (matched : RowsMatch (LiteralMachine.graph original) rows)
    (heads : HeadsMatch (LiteralMachine.graph original) rows matched)
    (rootMatches : RootsMatch (LiteralMachine.graph original) roots) (entry sourceSize : Nat)
    (capacity : 4096 * (original.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (constructionCode original width rows roots entry sourceSize))
    (room : entry + constructionSize original < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width (n + 1) rows roots) rows roots (fun _ : Fin (n + 1) => false))
    (sourceLength : sourceSize = state.heap.size)
    (heapRoom : sourceSize + (words original width).length + original.nodeCount < 2 ^ width) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 480 * (n + 1) * (original.countedSize + 1) ∧
      peak ≤ state.liveWords + 16 * (n + 1) * (original.countedSize + 1) ∧
      final.heap = state.heap ++ (words original width).toArray ++
        (List.ofFn (fun root : Fin original.nodeCount => boolWord width (LiteralMachine.summary original root).invalid)).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + constructionSize original) ∧ final.halted = false := by
  have all := physical
  unfold constructionCode at all
  have batchAt := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailAt := RawSharedOrdered.takeSuffix resident entry _ _ all
  have tailAt' : CodeAt resident (entry + 152 * (n + 1))
      ((SharedWitnessPark.code width (words original width).length).toArray ++
        LiteralConflict.jobsCode width
          (entry + 152 * (n + 1) + 2 * (words original width).length)
          (sourceSize + (words original width).length) (jobs original sourceSize)) := by simpa using tailAt
  have parkAt := RawSharedOrdered.takePrefix resident _ _ _ tailAt'
  have jobsAt := RawSharedOrdered.takeSuffix resident _ _ _ tailAt'
  obtain ⟨batched, batchTicks, batchPeak, batchTrace, batchTime, batchSpace, batchHeap, batchStack,
      batchOutput, batchPC, batchRunning, _⟩ :=
    execution resident state original rows roots matched heads rootMatches entry capacity batchAt
      (by unfold constructionSize at room; omega) position running heapStored
  obtain ⟨parked, parkTrace, parkHeap, parkStack, parkOutput, parkPC, parkRunning, _⟩ :=
    SharedWitnessPark.execution resident batched (words original width) state.stack (entry + 152 * (n + 1))
      batchPC batchRunning (by unfold constructionSize at room; rw [words_length]; omega)
      (by rw [batchHeap, ← sourceLength]; omega) batchStack
      (by
        intro offset below
        simpa only [List.getElem?_toArray] using parkAt ⟨offset, by simpa using below⟩)
  have parkedHeap : parked.heap = state.heap ++ (words original width).toArray := parkHeap.trans (by rw [batchHeap])
  have parkedSize : parked.heap.size = sourceSize + (words original width).length := by
    have bound := congrArg Array.size parkedHeap
    simp only [Array.size_append, List.size_toArray] at bound
    omega
  obtain ⟨final, jobTicks, jobTrace, jobTime, finalPC, finalHeap, finalStack, finalOutput, finalRunning, _⟩ :=
    LiteralConflict.jobs_execution resident parked
      (entry + 152 * (n + 1) + 2 * (words original width).length)
      (sourceSize + (words original width).length) (jobs original sourceSize) (values width original sourceSize)
      parkedSize.symm (by simpa using jobsAt) parkPC parkRunning
      (by simp only [jobs_work]; unfold constructionSize at room; rw [words_length]; omega)
      (by omega) (by rw [parkedSize, jobs_length]; exact heapRoom)
      (by rw [parkedHeap, sourceLength]; simpa using jobs_readable original state.heap (#[] : Array (Word width)))
      (by rw [parkedHeap, sourceLength]; simpa using jobs_sources original state.heap (#[] : Array (Word width)) (by omega))
  have batchLive : batched.liveWords = state.liveWords + (words original width).length := by
    simp only [State.liveWords, batchHeap, batchStack, batchOutput, List.length_append]; omega
  have parkLive : parked.liveWords = state.liveWords + (words original width).length := by
    simp only [State.liveWords, parkedHeap, parkStack, parkOutput, batchOutput, Array.size_append, List.size_toArray]; omega
  have size := original.countedSize_eq
  have nodes : n + 1 + 3 * original.nodeCount ≤ 4 * (original.countedSize + 1) := by omega
  have matrixBound : (words original width).length ≤ 4 * (n + 1) * (original.countedSize + 1) := by
    rw [words_length]
    simpa only [Nat.mul_assoc, Nat.mul_left_comm] using Nat.mul_le_mul_left (n + 1) nodes
  have workBound : LiteralConflict.work (jobs original sourceSize) ≤ 9 * (n + 1) * (original.countedSize + 1) := by
    rw [jobs_work]
    calc
      _ ≤ original.nodeCount * (9 * (n + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 9 * (n + 1) * original.nodeCount := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have columnBound : (n + 2) * (n + 1 + 3 * original.nodeCount) + 4 ≤
      16 * (n + 1) * (original.countedSize + 1) := by
    have first := Nat.mul_le_mul_left (n + 2) nodes
    have second := Nat.mul_le_mul_right (4 * (original.countedSize + 1)) (show n + 2 ≤ 2 * (n + 1) by omega)
    have positive : 0 < (n + 1) * (original.countedSize + 1) := Nat.mul_pos (by omega) (by omega)
    have upper := first.trans second
    have factor : (2 * (n + 1)) * (4 * (original.countedSize + 1)) =
        8 * ((n + 1) * (original.countedSize + 1)) := by
      calc
        _ = (2 * 4) * ((n + 1) * (original.countedSize + 1)) := by ac_rfl
        _ = _ := rfl
    rw [factor] at upper
    simp only [Nat.mul_assoc]
    omega
  simp only [Nat.mul_assoc] at matrixBound workBound batchTime columnBound
  refine ⟨final, batchTicks + (2 * (words original width).length + jobTicks),
    max batchPeak (max batched.liveWords (parked.liveWords + (jobs original sourceSize).length)),
    batchTrace.append (parkTrace.append jobTrace), ?_, ?_, ?_, finalStack.trans parkStack,
    finalOutput.trans (parkOutput.trans batchOutput), ?_, finalRunning⟩
  · simp only [Nat.mul_assoc]
    omega
  · rw [batchLive, parkLive, jobs_length]
    have tailBound : (words original width).length + original.nodeCount ≤
        16 * (n + 1) * (original.countedSize + 1) := by
      have nodeBound : original.nodeCount ≤ (n + 1) * (original.countedSize + 1) := by
        have mono := Nat.mul_le_mul_right (original.countedSize + 1) (show 1 ≤ n + 1 by omega)
        simp only [Nat.one_mul] at mono
        omega
      simp only [Nat.mul_assoc]
      omega
    simp only [Nat.mul_assoc] at tailBound ⊢
    omega
  · rw [finalHeap, parkedHeap, flags_correct _ _ (by omega)]
  · simpa only [jobs_work, words_length, constructionSize, Nat.add_assoc] using finalPC

theorem constructionSize_bound (original : DAG n) :
    constructionSize original ≤ 192 * ((n + 1) * (original.countedSize + 1)) := by
  have size := original.countedSize_eq
  have nodes : n + 1 + 3 * original.nodeCount ≤ 4 * (original.countedSize + 1) := by omega
  have matrix := Nat.mul_le_mul_left (n + 1) nodes
  have workBound : original.nodeCount * (3 + 9 * n) ≤ 9 * ((n + 1) * (original.countedSize + 1)) := by
    calc
      _ ≤ original.nodeCount * (9 * (n + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 9 * ((n + 1) * original.nodeCount) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left 9 (Nat.mul_le_mul_left (n + 1) (by omega))
  have baseline := Nat.mul_le_mul_left (152 * (n + 1)) (show 1 ≤ original.countedSize + 1 by omega)
  simp only [Nat.mul_one, Nat.mul_assoc] at baseline
  have factor : (n + 1) * (4 * (original.countedSize + 1)) = 4 * ((n + 1) * (original.countedSize + 1)) := by ac_rfl
  rw [factor] at matrix
  unfold constructionSize
  omega

theorem source_size_bound (original : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch (LiteralMachine.graph original) rows)
    (rootMatches : RootsMatch (LiteralMachine.graph original) roots) :
    (channelHeap (packetHeaderHeap width (n + 1) rows roots) rows roots (fun _ : Fin (n + 1) => false)).size ≤
      53 * (original.countedSize + 1) := by
  obtain ⟨children, guards⟩ := matched_incidence_lengths (LiteralMachine.graph original) rows matched
  have rootCount : roots.length = (LiteralMachine.graph original).roots.length := by rw [rootMatches]; simp
  have size := (LiteralMachine.graph original).countedSize_eq
  have linear := LiteralMachine.graph_size original
  simp only [channelHeap_size, cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount]
  have channels : (n + 1) ≤ (LiteralMachine.graph original).countedSize := by omega
  omega

def Width (original : DAG n) : Nat := SharedMachineCapacity.wordWidth 0 ((n + 1) * (original.countedSize + 1)) 0

def initial (n width : Nat) (rows : List Row) (roots : List Nat)
    (caller output : List (Word width)) : State width 8 where
  reg _ := word width 0
  heap := channelHeap (packetHeaderHeap width (n + 1) rows roots) rows roots (fun _ : Fin (n + 1) => false)
  stack := caller
  output := output
  pc := word width 0
  halted := false

def program (original : DAG n) (rows : List Row) (roots : List Nat) : Program (Width original) 8 :=
  constructionCode original (Width original) rows roots 0 (initial n (Width original) rows roots [] []).heap.size

/-- Capacity and instruction placement are discharged for this concrete
prepared-packet program. The caller frame and output are preserved. -/
theorem from_packet (original : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch (LiteralMachine.graph original) rows)
    (heads : HeadsMatch (LiteralMachine.graph original) rows matched)
    (rootMatches : RootsMatch (LiteralMachine.graph original) roots)
    (caller output : List (Word (Width original))) :
    ∃ final ticks peak,
      Execution (program original rows roots) (initial n (Width original) rows roots caller output) final ticks peak ∧
      ticks ≤ 480 * ((n + 1) * (original.countedSize + 1)) ∧
      programWords (program original rows roots) + peak ≤
        1024 * ((n + 1) * (original.countedSize + 1)) + caller.length + output.length ∧
      final.heap = (initial n (Width original) rows roots caller output).heap ++ (words original (Width original)).toArray ++
        (List.ofFn (fun root : Fin original.nodeCount => boolWord (Width original) (LiteralMachine.summary original root).invalid)).toArray ∧
      final.stack = caller ∧ final.output = output ∧ final.pc = word (Width original) (constructionSize original) ∧
      final.halted = false := by
  let start := initial n (Width original) rows roots caller output
  have capacity := SharedMachineCapacity.capacity 0 ((n + 1) * (original.countedSize + 1)) 0
  simp only [Nat.zero_add, Nat.add_zero] at capacity
  change 131072 * ((n + 1) * (original.countedSize + 1) + 1) < 2 ^ Width original at capacity
  have source := source_size_bound original rows roots matched rootMatches (width := Width original)
  have sourceBound : start.heap.size ≤ 53 * (original.countedSize + 1) := source
  have size := original.countedSize_eq
  have baseline : original.countedSize + 1 ≤ (n + 1) * (original.countedSize + 1) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (original.countedSize + 1) (show 1 ≤ n + 1 by omega)
  have matrix : (words original (Width original)).length ≤ 4 * ((n + 1) * (original.countedSize + 1)) := by
    rw [words_length]
    have bound := Nat.mul_le_mul_left (n + 1)
      (show n + 1 + 3 * original.nodeCount ≤ 4 * (original.countedSize + 1) by omega)
    simpa only [Nat.mul_assoc, Nat.mul_left_comm] using bound
  have codeSize := constructionSize_bound original
  have physical : CodeAt (program original rows roots) 0
      (constructionCode original (Width original) rows roots 0 start.heap.size) := by
    intro phase
    simp only [program, initial, start, Nat.zero_add]
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, result, pc, active⟩ :=
    construction_execution (program original rows roots) start original rows roots matched heads rootMatches 0 start.heap.size
      (by omega) physical (by omega) rfl rfl rfl rfl (by omega)
  refine ⟨final, ticks, peak, trace, by simpa only [Nat.mul_assoc] using time, ?_, heap, stack, result,
    by simpa only [Nat.zero_add] using pc, active⟩
  have code : programWords (program original rows roots) ≤ 768 * ((n + 1) * (original.countedSize + 1)) := by
    simp only [programWords, program, constructionCode_size]
    omega
  have live : start.liveWords ≤ 9 + 53 * (original.countedSize + 1) + caller.length + output.length := by
    dsimp only [State.liveWords, start, initial] at sourceBound ⊢
    omega
  have positive : 0 < (n + 1) * (original.countedSize + 1) := Nat.mul_pos (by omega) (by omega)
  simp only [Nat.mul_assoc] at space
  omega

end Controller.Extensions.LiteralColumns
