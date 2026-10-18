module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralSourceBatch
public import Controller.Cost.LiteralConflict
public import Controller.Cost.SharedWitnessPark
public import Controller.Extensions.LiteralColumns
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Literal columns constructed directly from the original source packet.
Positive and negative singleton probes share the source and scratch table;
one final pass propagates constant-zero ancestry. -/
namespace Controller.Extensions.LiteralSourceConstruction
open Controller.Decoder Controller.Decoder.DAG Controller.Cost Controller.Cost.GateProgram
open Controller.Cost.ForestIndexedOperands Controller.Cost.UniformDAGSource
open Controller.Cost.UniformDAGRun Controller.Cost.ForestInputPrefixStored
open Controller.Cost.ForestInputStored Controller.Cost.RawTransferLoops

def positive : LiteralSourceNode.Mode := ⟨true, false, false⟩
def negative : LiteralSourceNode.Mode := ⟨false, true, false⟩
def zero : LiteralSourceNode.Mode := ⟨false, false, true⟩

def matrix (graph : DAG n) (width : Nat) : List (Word width) :=
  LiteralSourceProbe.words zero graph (fun _ => false) width ++
    (LiteralSourceBatch.columns negative graph (List.finRange n) width ++
      LiteralSourceBatch.columns positive graph (List.finRange n) width)

@[simp] theorem matrix_length (graph : DAG n) :
    (matrix graph width).length = (2 * n + 1) * graph.nodeCount := by
  simp [matrix, Nat.add_mul, Nat.mul_assoc]; omega

def columnsCode (width n : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) : Program width 8 :=
  LiteralSourceBatch.code positive width n rows roots entry (List.finRange n) ++
    (LiteralSourceBatch.code negative width n rows roots (entry + 143 * n) (List.finRange n) ++
      LiteralSourceProbe.code zero width n rows roots (entry + 286 * n) (entry + 286 * n + 134))

@[simp] theorem columnsCode_size (width n : Nat) (rows : List Row) (roots : List Nat) (entry : Nat) :
    (columnsCode width n rows roots entry).size = 286 * n + 134 := by
  simp [columnsCode]; omega

set_option maxHeartbeats 800000 in
theorem columns_execution (resident : Program width 8) (state : State width 8)
    (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (entry : Nat)
    (capacity : 256 * (graph.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (columnsCode width n rows roots entry))
    (room : entry + 286 * n + 134 < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => false)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ (2 * n + 1) * (55 * graph.countedSize + 24) ∧
      peak ≤ state.liveWords + (2 * n + 2) * graph.nodeCount + 4 ∧
      final.heap = state.heap ∧ final.stack = matrix graph width ++ state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 286 * n + 134) ∧
      final.halted = false := by
  have all := physical
  unfold columnsCode at all
  have positiveAt := RawSharedOrdered.takePrefix resident entry _ _ all
  have restAt := RawSharedOrdered.takeSuffix resident entry _ _ all
  have negativeAt : CodeAt resident (entry + 143 * n)
      (LiteralSourceBatch.code negative width n rows roots (entry + 143 * n) (List.finRange n)) := by
    simpa only [LiteralSourceBatch.code_size, List.length_finRange] using
      RawSharedOrdered.takePrefix resident _ _ _ restAt
  have zeroAt : CodeAt resident (entry + 286 * n)
      (LiteralSourceProbe.code zero width n rows roots (entry + 286 * n) (entry + 286 * n + 134)) := by
    have offsets : entry + 143 * n + 143 * n = entry + 286 * n := by omega
    simpa only [LiteralSourceBatch.code_size, List.length_finRange, offsets] using
      RawSharedOrdered.takeSuffix resident _ _ _ restAt
  obtain ⟨positives, pt, pp, ptr, ptime, pspace, ph, ps, po, pc, pr⟩ :=
    LiteralSourceBatch.execution positive resident graph rows roots matched heads rootMatches
      (List.finRange n) entry state capacity positiveAt (by simp; omega) position running heapStored
  obtain ⟨negatives, nt, np, ntr, ntime, nspace, nh, ns, no, nc, nr⟩ :=
    LiteralSourceBatch.execution negative resident graph rows roots matched heads rootMatches
      (List.finRange n) (entry + 143 * n) positives capacity negativeAt (by simp; omega)
      (by simpa only [List.length_finRange] using pc) pr (ph.trans heapStored)
  obtain ⟨final, zt, zp, ztr, ztime, zspace, zh, zs, zo, zc, zr, _⟩ :=
    LiteralSourceProbe.execution zero resident negatives graph rows roots matched heads rootMatches
      (fun _ => false) (entry + 286 * n) (entry + 286 * n + 134) capacity zeroAt room
      (by simpa only [List.length_finRange, show entry + 143 * n + 143 * n = entry + 286 * n by omega] using nc)
      nr (nh.trans (ph.trans heapStored))
  have pl : positives.liveWords = state.liveWords + n * graph.nodeCount := by
    simp [State.liveWords, ph, ps, po]; omega
  have nl : negatives.liveWords = state.liveWords + 2 * n * graph.nodeCount := by
    simp [State.liveWords, nh, ns, no, ph, ps, po]; nlinarith
  refine ⟨final, pt + nt + zt, max (max pp np) zp, (ptr.append ntr).append ztr,
    ?_, ?_, zh.trans (nh.trans ph), ?_, zo.trans (no.trans po), zc, zr⟩
  · simp only [List.length_finRange] at ptime ntime
    nlinarith
  · simp only [List.length_finRange] at pspace nspace
    rw [pl] at nspace
    rw [nl] at zspace
    simp only [max_le_iff]
    constructor
    · constructor <;> nlinarith
    · nlinarith
  · simp only [zs, ns, ps, matrix, List.append_assoc]

theorem batch_cell (config : LiteralSourceNode.Mode) (graph : DAG n) (channel : Fin n)
    (root : Fin graph.nodeCount) :
    (LiteralSourceBatch.columns config graph (List.finRange n) width)[(n - 1 - channel.val) * graph.nodeCount + root.val]? =
      some (boolWord width (LiteralSourceRun.evalTable config graph (LiteralSourceBatch.single channel) root)) := by
  have columnBound : n - 1 - channel.val < (List.finRange n).reverse.length := by
    have := channel.isLt; simp; omega
  have selected : (List.finRange n).reverse[n - 1 - channel.val] = channel := by
    apply Fin.ext
    simp only [List.getElem_reverse, List.length_finRange, List.getElem_finRange]
    change n - 1 - (n - 1 - channel.val) = channel.val
    have := channel.isLt; omega
  unfold LiteralSourceBatch.columns
  rw [LiteralColumns.flatMap_cell _ _ graph.nodeCount
    (fun _ _ => LiteralSourceProbe.words_length _ _ _) ⟨_, columnBound⟩ root.val root.isLt]
  rw [selected]
  simp only [LiteralSourceProbe.words, List.getElem?_ofFn]
  split
  · rfl
  · rename_i invalid; exact (invalid root.isLt).elim

def signAddress (graph : DAG n) (channel : Fin n) (root : Fin graph.nodeCount) (neg : Bool) : Nat :=
  graph.nodeCount + (if neg then 0 else n * graph.nodeCount) +
    (n - 1 - channel.val) * graph.nodeCount + root.val

theorem sign_cell (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (channel : Fin n) (root : Fin graph.nodeCount) (neg : Bool) :
    (matrix graph width)[signAddress graph channel root neg]? =
      some (boolWord width (if neg then decide (channel ∈ (LiteralMachine.summary graph root).negative)
        else decide (channel ∈ (LiteralMachine.summary graph root).positive))) := by
  have inside : (n - 1 - channel.val) * graph.nodeCount + root.val < n * graph.nodeCount := by
    have sub : n - 1 - channel.val + 1 ≤ n := by have := channel.isLt; omega
    have mult := Nat.mul_le_mul_right graph.nodeCount sub
    have := root.isLt
    nlinarith
  have assignment : LiteralSourceBatch.single channel = (fun c => decide (c.castSucc = channel.castSucc)) := by
    funext c
    simp [LiteralSourceBatch.single, SharedCandidateProbe.enabled, Fin.ext_iff, eq_comm]
  have pconfig : positive = LiteralSource.mode channel.castSucc 0 := by simp [positive, LiteralSource.mode]
  have nconfig : negative = LiteralSource.mode channel.castSucc 1 := by simp [negative, LiteralSource.mode]
  have pcell := batch_cell positive (width := width) graph channel root
  have ncell := batch_cell negative (width := width) graph channel root
  rw [assignment, pconfig, LiteralSourceRun.table_flags graph noOr] at pcell
  rw [assignment, nconfig, LiteralSourceRun.table_flags graph noOr] at ncell
  rw [← pconfig] at pcell
  rw [← nconfig] at ncell
  simp only [matrix, signAddress]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [LiteralSourceProbe.words_length]
  cases neg with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [List.getElem?_append_right (by simp; omega)]
    have index : graph.nodeCount + n * graph.nodeCount + (n - 1 - channel.val) * graph.nodeCount + root.val -
        graph.nodeCount - (LiteralSourceBatch.columns negative graph (List.finRange n) width).length =
        (n - 1 - channel.val) * graph.nodeCount + root.val := by simp; omega
    rw [index]
    simpa [LiteralMachine.flags, LiteralMachine.bit, ← Fin.ext_iff] using pcell
  | true =>
    simp only [ite_true, Nat.add_zero]
    have index : graph.nodeCount + (n - 1 - channel.val) * graph.nodeCount + root.val - graph.nodeCount =
        (n - 1 - channel.val) * graph.nodeCount + root.val := by omega
    rw [index, List.getElem?_append_left (by simpa using inside)]
    simpa [LiteralMachine.flags, LiteralMachine.bit, ← Fin.ext_iff] using ncell

theorem zero_cell (graph : DAG n) (noOr : GateBasis.NoDisjunction graph) (root : Fin graph.nodeCount) :
    (matrix graph width)[root.val]? = some (boolWord width (LiteralMachine.summary graph root).zero) := by
  rw [matrix, List.getElem?_append_left (by simpa using root.isLt)]
  have config : zero = LiteralSource.mode (Fin.last n) 2 := by simp [zero, LiteralSource.mode]
  have assignment : (fun _ : Fin n => false) = (fun c => decide (c.castSucc = Fin.last n)) := by
    funext c; simp
  simp only [LiteralSourceProbe.words, List.getElem?_ofFn]
  split
  · rw [config, assignment, LiteralSourceRun.table_flags graph noOr]
    simp [LiteralMachine.flags]
  · rename_i invalid; exact (invalid root.isLt).elim

def read (source : List (Word width)) (index : Nat) : Bool :=
  decide (source[index]? = some (boolWord width true))

theorem read_sign (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (channel : Fin n) (root : Fin graph.nodeCount) (neg : Bool) (booleanRoom : 1 < 2 ^ width) :
    read (matrix graph width) (signAddress graph channel root neg) =
      if neg then decide (channel ∈ (LiteralMachine.summary graph root).negative)
      else decide (channel ∈ (LiteralMachine.summary graph root).positive) := by
  rw [read, sign_cell graph noOr]
  cases h : (if neg then decide (channel ∈ (LiteralMachine.summary graph root).negative)
      else decide (channel ∈ (LiteralMachine.summary graph root).positive)) <;>
    simp [boolWord, word, Nat.mod_eq_of_lt booleanRoom, Nat.mod_eq_of_lt (Nat.two_pow_pos width)]

theorem read_zero (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (root : Fin graph.nodeCount) (booleanRoom : 1 < 2 ^ width) :
    read (matrix graph width) root.val = (LiteralMachine.summary graph root).zero := by
  rw [read, zero_cell graph noOr]
  cases h : (LiteralMachine.summary graph root).zero <;>
    simp [boolWord, word, Nat.mod_eq_of_lt booleanRoom, Nat.mod_eq_of_lt (Nat.two_pow_pos width)]

def decode (graph : DAG n) (source : List (Word width)) (root : Fin graph.nodeCount) : LiteralMachine.Raw n where
  positive := Finset.univ.filter fun c => read source (signAddress graph c root false)
  negative := Finset.univ.filter fun c => read source (signAddress graph c root true)
  zero := read source root.val

theorem decode_matrix (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (root : Fin graph.nodeCount) (booleanRoom : 1 < 2 ^ width) :
    decode graph (matrix graph width) root = LiteralMachine.summary graph root := by
  apply LiteralMachine.Raw.ext
  · ext c; simp [decode, read_sign _ noOr _ _ _ booleanRoom]
  · ext c; simp [decode, read_sign _ noOr _ _ _ booleanRoom]
  · simp [decode, read_zero _ noOr _ booleanRoom]

theorem signAddress_bound (graph : DAG n) (channel : Fin n) (root : Fin graph.nodeCount) (neg : Bool) :
    signAddress graph channel root neg < (matrix graph width).length := by
  have sub : n - 1 - channel.val + 1 ≤ n := by have := channel.isLt; omega
  have mult := Nat.mul_le_mul_right graph.nodeCount sub
  have ri := root.isLt
  rw [matrix_length]
  unfold signAddress
  cases neg <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> nlinarith

theorem zeroAddress_bound (graph : DAG n) (root : Fin graph.nodeCount) :
    root.val < (matrix graph width).length := by
  rw [matrix_length]
  have := root.isLt
  nlinarith

def pairs (graph : DAG n) (base : Nat) (root : Fin graph.nodeCount) : List (Nat × Nat) :=
  (List.finRange n).map fun c => (base + signAddress graph c root false, base + signAddress graph c root true)

def jobs (graph : DAG n) (base : Nat) : List LiteralConflict.Job :=
  List.ofFn fun root : Fin graph.nodeCount => ⟨base + root.val, pairs graph base root⟩

def values (width : Nat) (graph : DAG n) (base index : Nat) : Bool := read (matrix graph width) (index - base)

theorem flags_correct (graph : DAG n) (noOr : GateBasis.NoDisjunction graph) (base : Nat)
    (booleanRoom : 1 < 2 ^ width) :
    LiteralConflict.flags width (values width graph base) (jobs graph base) =
      List.ofFn (fun root : Fin graph.nodeCount => boolWord width (LiteralMachine.summary graph root).invalid) := by
  simp only [jobs, LiteralConflict.flags, List.map_ofFn]
  congr 1
  funext root
  simp [values, pairs, LiteralConflict.collision, read_zero _ noOr _ booleanRoom,
    read_sign _ noOr _ _ _ booleanRoom, List.any_map, Function.comp_def, LiteralMachine.Raw.invalid]

@[simp] theorem jobs_length (graph : DAG n) (base : Nat) : (jobs graph base).length = graph.nodeCount := by simp [jobs]

@[simp] theorem jobs_work (graph : DAG n) (base : Nat) :
    LiteralConflict.work (jobs graph base) = graph.nodeCount * (3 + 9 * n) := by
  simp [LiteralConflict.work, jobs, pairs, List.sum_ofFn]

theorem stored_matrix_cell (graph : DAG n) (frame suffix : Array (Word width))
    (index : Nat) (inside : index < (matrix graph width).length) :
    (frame ++ (matrix graph width).toArray ++ suffix)[frame.size + index]? = (matrix graph width)[index]? := by
  rw [Array.getElem?_append_left (by simp only [Array.size_append, List.size_toArray]; omega),
    Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_toArray]

theorem jobs_readable (graph : DAG n) (frame suffix : Array (Word width)) :
    ∀ job ∈ jobs graph frame.size,
      job.zeroAddress < (frame ++ (matrix graph width).toArray ++ suffix).size ∧
        ∀ pair ∈ job.pairs, pair.1 < (frame ++ (matrix graph width).toArray ++ suffix).size ∧
          pair.2 < (frame ++ (matrix graph width).toArray ++ suffix).size := by
  intro job member
  obtain ⟨root, rfl⟩ := List.mem_ofFn.mp member
  refine ⟨?_, ?_⟩
  · have := zeroAddress_bound graph root (width := width)
    simp only [Array.size_append, List.size_toArray]; omega
  · intro pair member
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp member
    have pos := signAddress_bound graph c root false (width := width)
    have neg := signAddress_bound graph c root true (width := width)
    simp only [Array.size_append, List.size_toArray]
    constructor <;> omega

theorem jobs_sources (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (frame suffix : Array (Word width)) (booleanRoom : 1 < 2 ^ width) :
    ∀ job ∈ jobs graph frame.size,
      (frame ++ (matrix graph width).toArray ++ suffix)[job.zeroAddress]? =
        some (boolWord width (values width graph frame.size job.zeroAddress)) ∧
      ∀ pair ∈ job.pairs,
        (frame ++ (matrix graph width).toArray ++ suffix)[pair.1]? =
          some (boolWord width (values width graph frame.size pair.1)) ∧
        (frame ++ (matrix graph width).toArray ++ suffix)[pair.2]? =
          some (boolWord width (values width graph frame.size pair.2)) := by
  intro job member
  obtain ⟨root, rfl⟩ := List.mem_ofFn.mp member
  refine ⟨?_, ?_⟩
  · simpa [values, read_zero _ noOr _ booleanRoom, zero_cell _ noOr] using
      stored_matrix_cell graph frame suffix root.val (zeroAddress_bound graph root)
  · intro pair member
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp member
    constructor
    · simpa [values, read_sign _ noOr _ _ _ booleanRoom, sign_cell _ noOr] using
        stored_matrix_cell graph frame suffix (signAddress graph c root false) (signAddress_bound graph c root false)
    · simpa [values, read_sign _ noOr _ _ _ booleanRoom, sign_cell _ noOr] using
        stored_matrix_cell graph frame suffix (signAddress graph c root true) (signAddress_bound graph c root true)

def constructionCode (original : DAG n) (width : Nat) (rows : List Row) (roots : List Nat)
    (entry sourceSize : Nat) : Program width 8 :=
  columnsCode width n rows roots entry ++
    ((SharedWitnessPark.code width ((2 * n + 1) * original.nodeCount)).toArray ++
      LiteralConflict.jobsCode width
        (entry + (286 * n + 134) + 2 * ((2 * n + 1) * original.nodeCount))
        (sourceSize + (2 * n + 1) * original.nodeCount) (jobs original sourceSize))

def constructionSize (original : DAG n) : Nat :=
  (286 * n + 134) + 2 * ((2 * n + 1) * original.nodeCount) + original.nodeCount * (3 + 9 * n)

@[simp] theorem constructionCode_size (original : DAG n) (width : Nat) (rows : List Row) (roots : List Nat)
    (entry sourceSize : Nat) :
    (constructionCode original width rows roots entry sourceSize).size = constructionSize original := by
  simp [constructionCode, constructionSize, Nat.add_assoc]

/-- The graph parameter contributes only its node count to the generated
instruction array; the source-layout parameters are explicit. -/
theorem constructionCode_independent (left right : DAG n) (same : left.nodeCount = right.nodeCount)
    (width : Nat) (rows : List Row) (roots : List Nat) (entry sourceSize : Nat) :
    constructionCode left width rows roots entry sourceSize =
      constructionCode right width rows roots entry sourceSize := by
  rcases left with ⟨leftCount, leftNodes, leftRoots⟩
  rcases right with ⟨rightCount, rightNodes, rightRoots⟩
  dsimp at same
  subst rightCount
  rfl

set_option maxHeartbeats 800000 in
/-- A single fetched run constructs all sign columns and all normalized zero
flags. It reads the original graph's retained input packet. -/
theorem construction_execution (resident : Program width 8) (state : State width 8) (original : DAG n)
    (noOr : GateBasis.NoDisjunction original) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch original rows)
    (heads : HeadsMatch original rows matched)
    (rootMatches : RootsMatch original roots) (entry sourceSize : Nat)
    (capacity : 4096 * (original.countedSize + 1) < 2 ^ width)
    (physical : CodeAt resident entry (constructionCode original width rows roots entry sourceSize))
    (room : entry + constructionSize original < 2 ^ width)
    (position : state.pc = word width entry) (running : state.halted = false)
    (heapStored : state.heap = channelHeap (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => false))
    (sourceLength : sourceSize = state.heap.size)
    (heapRoom : sourceSize + (matrix original width).length + original.nodeCount < 2 ^ width) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ 480 * (n + 1) * (original.countedSize + 1) ∧
      peak ≤ state.liveWords + 16 * (n + 1) * (original.countedSize + 1) ∧
      final.heap = state.heap ++ (matrix original width).toArray ++
        (List.ofFn (fun root : Fin original.nodeCount => boolWord width (LiteralMachine.summary original root).invalid)).toArray ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + constructionSize original) ∧ final.halted = false := by
  have all := physical
  unfold constructionCode at all
  have batchAt := RawSharedOrdered.takePrefix resident entry _ _ all
  have tailAt := RawSharedOrdered.takeSuffix resident entry _ _ all
  have tailAt' : CodeAt resident (entry + (286 * n + 134))
      ((SharedWitnessPark.code width (matrix original width).length).toArray ++
        LiteralConflict.jobsCode width
          (entry + (286 * n + 134) + 2 * (matrix original width).length)
          (sourceSize + (matrix original width).length) (jobs original sourceSize)) := by simpa only [columnsCode_size, matrix_length, Nat.add_assoc] using tailAt
  have parkAt := RawSharedOrdered.takePrefix resident _ _ _ tailAt'
  have jobsAt := RawSharedOrdered.takeSuffix resident _ _ _ tailAt'
  obtain ⟨batched, batchTicks, batchPeak, batchTrace, batchTime, batchSpace, batchHeap, batchStack,
      batchOutput, batchPC, batchRunning⟩ :=
    columns_execution resident state original rows roots matched heads rootMatches entry (by omega) batchAt
      (by unfold constructionSize at room; omega) position running heapStored
  obtain ⟨parked, parkTrace, parkHeap, parkStack, parkOutput, parkPC, parkRunning, _⟩ :=
    SharedWitnessPark.execution resident batched (matrix original width) state.stack (entry + (286 * n + 134))
      (by simpa only [Nat.add_assoc] using batchPC) batchRunning (by unfold constructionSize at room; rw [matrix_length]; omega)
      (by rw [batchHeap, ← sourceLength]; omega) batchStack
      (by
        intro offset below
        simpa only [List.getElem?_toArray] using parkAt ⟨offset, by simpa using below⟩)
  have parkedHeap : parked.heap = state.heap ++ (matrix original width).toArray := parkHeap.trans (by rw [batchHeap])
  have parkedSize : parked.heap.size = sourceSize + (matrix original width).length := by
    have bound := congrArg Array.size parkedHeap
    simp only [Array.size_append, List.size_toArray] at bound
    omega
  obtain ⟨final, jobTicks, jobTrace, jobTime, finalPC, finalHeap, finalStack, finalOutput, finalRunning, _⟩ :=
    LiteralConflict.jobs_execution resident parked
      (entry + (286 * n + 134) + 2 * (matrix original width).length)
      (sourceSize + (matrix original width).length) (jobs original sourceSize) (values width original sourceSize)
      parkedSize.symm (by simpa using jobsAt) parkPC parkRunning
      (by simp only [jobs_work]; unfold constructionSize at room; rw [matrix_length]; omega)
      (by omega) (by rw [parkedSize, jobs_length]; exact heapRoom)
      (by rw [parkedHeap, sourceLength]; simpa using jobs_readable original state.heap (#[] : Array (Word width)))
      (by rw [parkedHeap, sourceLength]; simpa using jobs_sources original noOr state.heap (#[] : Array (Word width)) (by omega))
  have batchLive : batched.liveWords = state.liveWords + (matrix original width).length := by
    simp only [State.liveWords, batchHeap, batchStack, batchOutput, List.length_append]; omega
  have parkLive : parked.liveWords = state.liveWords + (matrix original width).length := by
    simp only [State.liveWords, parkedHeap, parkStack, parkOutput, batchOutput, Array.size_append, List.size_toArray]; omega
  have size := original.countedSize_eq
  have matrixBound : (matrix original width).length ≤ 4 * (n + 1) * (original.countedSize + 1) := by
    rw [matrix_length]
    have mult := Nat.mul_le_mul_left (2 * n + 1) (show original.nodeCount ≤ original.countedSize + 1 by omega)
    nlinarith
  have batchTime' : batchTicks ≤ 448 * (n + 1) * (original.countedSize + 1) := by
    nlinarith
  have workBound : LiteralConflict.work (jobs original sourceSize) ≤ 9 * (n + 1) * (original.countedSize + 1) := by
    rw [jobs_work]
    calc
      _ ≤ original.nodeCount * (9 * (n + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 9 * (n + 1) * original.nodeCount := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have columnBound : (2 * n + 2) * original.nodeCount + 4 ≤
      16 * (n + 1) * (original.countedSize + 1) := by
    have mult := Nat.mul_le_mul_left (2 * n + 2) (show original.nodeCount ≤ original.countedSize + 1 by omega)
    nlinarith
  simp only [Nat.mul_assoc] at matrixBound workBound batchTime' columnBound
  refine ⟨final, batchTicks + (2 * (matrix original width).length + jobTicks),
    max batchPeak (max batched.liveWords (parked.liveWords + (jobs original sourceSize).length)),
    batchTrace.append (parkTrace.append jobTrace), ?_, ?_, ?_, finalStack.trans parkStack,
    finalOutput.trans (parkOutput.trans batchOutput), ?_, finalRunning⟩
  · simp only [Nat.mul_assoc]
    omega
  · rw [batchLive, parkLive, jobs_length]
    have tailBound : (matrix original width).length + original.nodeCount ≤
        16 * (n + 1) * (original.countedSize + 1) := by
      have nodeBound : original.nodeCount ≤ (n + 1) * (original.countedSize + 1) := by
        have mono := Nat.mul_le_mul_right (original.countedSize + 1) (show 1 ≤ n + 1 by omega)
        simp only [Nat.one_mul] at mono
        omega
      simp only [Nat.mul_assoc]
      omega
    simp only [Nat.mul_assoc] at tailBound ⊢
    omega
  · rw [finalHeap, parkedHeap, flags_correct _ noOr _ (by omega)]
  · simpa only [jobs_work, matrix_length, constructionSize, Nat.add_assoc] using finalPC

theorem constructionSize_bound (original : DAG n) :
    constructionSize original ≤ 512 * ((n + 1) * (original.countedSize + 1)) := by
  have size := original.countedSize_eq
  have nodes : original.nodeCount ≤ original.countedSize := by omega
  have channels : n ≤ original.countedSize := by omega
  unfold constructionSize
  nlinarith

theorem source_size_bound (original : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch original rows) (rootMatches : RootsMatch original roots) :
    (channelHeap (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => false)).size ≤
      7 * (original.countedSize + 1) := by
  obtain ⟨children, guards⟩ := matched_incidence_lengths original rows matched
  have rootCount : roots.length = original.roots.length := by rw [rootMatches]; simp
  have size := original.countedSize_eq
  simp only [channelHeap_size, cacheHeap_size, packetHeaderHeap_size, matched.length_eq, children, guards, rootCount]
  omega

def Width (original : DAG n) : Nat := SharedMachineCapacity.wordWidth 0 ((n + 1) * (original.countedSize + 1)) 0

def initial (n width : Nat) (rows : List Row) (roots : List Nat)
    (caller output : List (Word width)) : State width 8 where
  reg _ := word width 0
  heap := channelHeap (packetHeaderHeap width n rows roots) rows roots (fun _ : Fin n => false)
  stack := caller
  output := output
  pc := word width 0
  halted := false

def program (original : DAG n) (rows : List Row) (roots : List Nat) : Program (Width original) 8 :=
  constructionCode original (Width original) rows roots 0 (initial n (Width original) rows roots [] []).heap.size

/-- Capacity and instruction placement are discharged for this concrete
original-source program. The caller frame and output are preserved. -/
theorem from_source (original : DAG n) (noOr : GateBasis.NoDisjunction original) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch original rows)
    (heads : HeadsMatch original rows matched)
    (rootMatches : RootsMatch original roots)
    (caller output : List (Word (Width original))) :
    ∃ final ticks peak,
      Execution (program original rows roots) (initial n (Width original) rows roots caller output) final ticks peak ∧
      ticks ≤ 480 * ((n + 1) * (original.countedSize + 1)) ∧
      programWords (program original rows roots) + peak ≤
        4096 * ((n + 1) * (original.countedSize + 1)) + caller.length + output.length ∧
      final.heap = (initial n (Width original) rows roots caller output).heap ++ (matrix original (Width original)).toArray ++
        (List.ofFn (fun root : Fin original.nodeCount => boolWord (Width original) (LiteralMachine.summary original root).invalid)).toArray ∧
      final.stack = caller ∧ final.output = output ∧ final.pc = word (Width original) (constructionSize original) ∧
      final.halted = false := by
  let start := initial n (Width original) rows roots caller output
  have capacity := SharedMachineCapacity.capacity 0 ((n + 1) * (original.countedSize + 1)) 0
  simp only [Nat.zero_add, Nat.add_zero] at capacity
  change 131072 * ((n + 1) * (original.countedSize + 1) + 1) < 2 ^ Width original at capacity
  have source := source_size_bound original rows roots matched rootMatches (width := Width original)
  have sourceBound : start.heap.size ≤ 7 * (original.countedSize + 1) := source
  have size := original.countedSize_eq
  have baseline : original.countedSize + 1 ≤ (n + 1) * (original.countedSize + 1) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (original.countedSize + 1) (show 1 ≤ n + 1 by omega)
  have matrixBound : (matrix original (Width original)).length ≤ 4 * ((n + 1) * (original.countedSize + 1)) := by
    rw [matrix_length]
    have mult := Nat.mul_le_mul_left (2 * n + 1) (show original.nodeCount ≤ original.countedSize + 1 by omega)
    nlinarith
  have codeSize := constructionSize_bound original
  have physical : CodeAt (program original rows roots) 0
      (constructionCode original (Width original) rows roots 0 start.heap.size) := by
    intro phase
    simp only [program, initial, start, Nat.zero_add]
  obtain ⟨final, ticks, peak, trace, time, space, heap, stack, result, pc, active⟩ :=
    construction_execution (program original rows roots) start original noOr rows roots matched heads rootMatches 0 start.heap.size
      (by omega) physical (by omega) rfl rfl rfl rfl (by omega)
  refine ⟨final, ticks, peak, trace, by simpa only [Nat.mul_assoc] using time, ?_, heap, stack, result,
    by simpa only [Nat.zero_add] using pc, active⟩
  have code : programWords (program original rows roots) ≤ 2048 * ((n + 1) * (original.countedSize + 1)) := by
    simp only [programWords, program, constructionCode_size]
    omega
  have live : start.liveWords ≤ 9 + 7 * (original.countedSize + 1) + caller.length + output.length := by
    dsimp only [State.liveWords, start, initial] at sourceBound ⊢
    omega
  have positive : 0 < (n + 1) * (original.countedSize + 1) := Nat.mul_pos (by omega) (by omega)
  simp only [Nat.mul_assoc] at space
  omega

end Controller.Extensions.LiteralSourceConstruction
