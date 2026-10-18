module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralRoot

@[expose] public section

/-! One root's fetched decision. Register 4 holds the root's node id. The
routine leaves through one of three caller labels: no witness, the kept
positive literals, or one channel (in register 1). -/
namespace Controller.Extensions.LiteralRootRun
open Controller.Decoder Controller.Cost Controller.Cost.EnumerationSteps
open Controller.Extensions.LiteralScan Controller.Extensions.LiteralDecision
open Controller.Extensions.LiteralRoot Controller.Extensions.LiteralTests

variable {n width : Nat}

/-- Read the cell at `offset + reg 4`; jump to `onFalse` on zero, else set
register 1 and jump to `onTrue`. -/
def readCode (offset onFalse onTrue value : Nat) : List (Instruction width 8) :=
  [.constant 5 (word width offset), .add 5 5 4, .load 3 5, .branchZero 3 (word width onFalse),
    .constant 1 (word width value), .constant 0 (word width 0), .branchZero 0 (word width onTrue)]

@[simp] theorem readCode_length (offset onFalse onTrue value : Nat) :
    (readCode (width := width) offset onFalse onTrue value).length = 7 := rfl

set_option maxHeartbeats 1000000 in
theorem read_execution (program : Program width 8) (state : State width 8)
    (entry offset onFalse onTrue value root : Nat) (bit : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + offset + root + value + 8 < 2 ^ width) (rootReg : state.reg 4 = word width root)
    (cell : state.heap[offset + root]? = some (boolWord width bit))
    (present : SharedRootRead.BlockAt program entry (readCode offset onFalse onTrue value)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 7 ∧ final.halted = false ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.reg 4 = state.reg 4 ∧
      (if bit then final.pc = word width onTrue ∧ final.reg 1 = word width value
        else final.pc = word width onFalse) := by
  have f : ∀ i (small : i < 7), program[entry + i]? = (readCode (width := width) offset onFalse onTrue value)[i]? :=
    fun i small => present i (by simpa using small)
  have boolRoom : 1 < 2 ^ width := by omega
  obtain ⟨s1, t1, pc1, v1, h1, st1, o1, r1, fr1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry offset 5 state position running (by omega)
      (by simpa [readCode] using f 0 (by decide))
  obtain ⟨s2, t2, pc2, v2, h2, st2, o2, r2, fr2⟩ :=
    add_execution program s1 (entry + 1) 5 5 4 pc1 r1 (by omega) (by simpa [readCode] using f 1 (by decide))
  have address : (s2.reg 5).val = offset + root := by
    rw [v2, v1, fr1 4 (by decide), rootReg, word_val offset (by omega), word_val root (by omega),
      word_val (offset + root) (by omega)]
  have inside : (s2.reg 5).val < s2.heap.size := by
    rw [address, h2, h1]; exact (Array.getElem?_eq_some_iff.mp cell).1
  obtain ⟨s3, t3, pc3, v3, h3, st3, o3, r3, fr3⟩ :=
    load_execution program s2 (entry + 1 + 1) 3 5 pc2 r2 (by omega) inside
      (by simpa [readCode] using f 2 (by decide))
  have loaded : s3.reg 3 = boolWord width bit := by
    rw [v3]
    have c := cell
    rw [← h1, ← h2, ← address, Array.getElem?_eq_getElem inside] at c
    exact Option.some.inj c
  have live : ∀ s : State width 8, s.heap = state.heap → s.stack = state.stack → s.output = state.output →
      s.liveWords = state.liveWords := by
    intro s h st o; simp only [State.liveWords, h, st, o]
  have l1 := live s1 h1 st1 o1
  have l2 := live s2 (h2.trans h1) (st2.trans st1) (o2.trans o1)
  have l3 := live s3 (by rw [h3, h2, h1]) (by rw [st3, st2, st1]) (by rw [o3, o2, o1])
  have reg4 : s3.reg 4 = state.reg 4 := by
    rw [fr3 4 (by decide), fr2 4 (by decide), fr1 4 (by decide)]
  cases bit with
  | false =>
    obtain ⟨s4, t4, pc4, h4, st4, o4, r4, fr4⟩ :=
      branch_taken program s3 (entry + 1 + 1 + 1) onFalse 3 pc3 r3 (by omega)
        (by rw [loaded]; simp [boolWord, word]) (by simpa [readCode] using f 3 (by decide))
    have joined := t1.append (t2.append (t3.append t4))
    rw [l1, l2, l3] at joined
    simp only [Nat.max_self] at joined
    exact ⟨s4, _, joined, by omega, r4, by rw [h4, h3, h2, h1], by rw [st4, st3, st2, st1],
      by rw [o4, o3, o2, o1], by rw [fr4, reg4], by simpa using pc4⟩
  | true =>
    obtain ⟨s4, t4, pc4, h4, st4, o4, r4, fr4⟩ :=
      branch_skipped program s3 (entry + 1 + 1 + 1) onFalse 3 pc3 r3 (by omega)
        (by rw [loaded]; simp [boolWord, word, Nat.mod_eq_of_lt boolRoom]) (by simpa [readCode] using f 3 (by decide))
    obtain ⟨s5, t5, pc5, v5, h5, st5, o5, r5, fr5⟩ :=
      SharedEvaluationReclaim.constant_execution program (entry + 1 + 1 + 1 + 1) value 1 s4 pc4 r4 (by omega)
        (by simpa [readCode] using f 4 (by decide))
    obtain ⟨s6, t6, pc6, h6, st6, o6, r6, fr6⟩ :=
      jump_execution program s5 (entry + 1 + 1 + 1 + 1 + 1) onTrue pc5 r5 (by omega)
        (by simpa [readCode] using f 5 (by decide)) (by simpa [readCode] using f 6 (by decide))
    have l4 := live s4 (by rw [h4, h3, h2, h1]) (by rw [st4, st3, st2, st1]) (by rw [o4, o3, o2, o1])
    have l5 := live s5 (by rw [h5, h4, h3, h2, h1]) (by rw [st5, st4, st3, st2, st1]) (by rw [o5, o4, o3, o2, o1])
    have joined := t1.append (t2.append (t3.append (t4.append (t5.append t6))))
    rw [l1, l2, l3, l4, l5] at joined
    simp only [Nat.max_self] at joined
    refine ⟨s6, _, joined, by omega, r6, by rw [h6, h5, h4, h3, h2, h1], by rw [st6, st5, st4, st3, st2, st1],
      by rw [o6, o5, o4, o3, o2, o1], by rw [fr6 4 (by decide), fr5 4 (by decide), fr4, reg4], ?_⟩
    simp only [ite_true]
    exact ⟨pc6, by rw [fr6 1 (by decide), v5]⟩

/-- An execution that changes only registers other than 4 and keeps the peak at the start. -/
def Quiet (program : Program width 8) (start final : State width 8) (bound : Nat) : Prop :=
  ∃ ticks, Execution program start final ticks start.liveWords ∧ ticks ≤ bound ∧ final.halted = false ∧
    final.heap = start.heap ∧ final.stack = start.stack ∧ final.output = start.output ∧
    final.reg 4 = start.reg 4

theorem Quiet.trans {program : Program width 8} {start middle final : State width 8} {first second : Nat}
    (left : Quiet program start middle first) (right : Quiet program middle final second) :
    Quiet program start final (first + second) := by
  obtain ⟨t1, e1, b1, _, h1, s1, o1, r1⟩ := left
  obtain ⟨t2, e2, b2, run, h2, s2, o2, r2⟩ := right
  have live : middle.liveWords = start.liveWords := by simp only [State.liveWords, h1, s1, o1]
  rw [live] at e2
  have joined := e1.append e2
  rw [Nat.max_self] at joined
  exact ⟨t1 + t2, joined, by omega, run, h2.trans h1, s2.trans s1, o2.trans o1, r2.trans r1⟩

theorem Quiet.mono {program : Program width 8} {start final : State width 8} {small large : Nat}
    (q : Quiet program start final small) (le : small ≤ large) : Quiet program start final large := by
  obtain ⟨t, e, b, rest⟩ := q
  exact ⟨t, e, by omega, rest⟩

theorem read_quiet (program : Program width 8) (state : State width 8)
    (entry offset onFalse onTrue value root : Nat) (bit : Bool)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + offset + root + value + 8 < 2 ^ width) (rootReg : state.reg 4 = word width root)
    (cell : state.heap[offset + root]? = some (boolWord width bit))
    (present : SharedRootRead.BlockAt program entry (readCode offset onFalse onTrue value)) :
    ∃ final, Quiet program state final 7 ∧
      (if bit then final.pc = word width onTrue ∧ final.reg 1 = word width value
        else final.pc = word width onFalse) := by
  obtain ⟨final, ticks, e, b, run, h, st, o, r4, result⟩ :=
    read_execution program state entry offset onFalse onTrue value root bit position running room rootReg cell present
  exact ⟨final, ⟨ticks, e, b, run, h, st, o, r4⟩, result⟩

theorem call_quiet (graph : DAG n) (noOr : GateBasis.NoDisjunction graph) (program : Program width 8)
    (test : List (Instruction width 8)) (bound : Nat) (hit : Nat → Bool → Bool → Bool) (spec : TestSpec test bound hit)
    (base first count entry found missing : Nat) (root : Fin graph.nodeCount) (state : State width 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (range : first + count ≤ n)
    (room : base + (2 * n + 1) * graph.nodeCount + entry + test.length + 19 < 2 ^ width)
    (rootReg : state.reg 4 = word width root.val)
    (stored : MatrixAt state.heap base graph)
    (present : SharedRootRead.BlockAt program entry (callCode test n graph.nodeCount base first count entry found missing)) :
    ∃ final, Quiet program state final (count * (bound + 13) + 7) ∧
      (match firstHit (fun d => hit d (posBit (LiteralMachine.summary graph root) d)
          (negBit (LiteralMachine.summary graph root) d)) first count with
        | some d => final.pc = word width found ∧ final.reg 1 = word width d
        | none => final.pc = word width missing) := by
  obtain ⟨final, ticks, e, b, run, h, st, o, r4, result⟩ :=
    call_execution graph noOr program test bound hit spec base first count entry found missing root state position
      running range room rootReg stored present
  exact ⟨final, ⟨ticks, e, b, run, h, st, o, r4⟩, result⟩

/-- Layout of the root routine. -/
def nonzero (entry : Nat) : Nat := entry + 7
def healthyEntry (entry : Nat) : Nat := nonzero entry + 49
def unhealthyEntry (entry : Nat) : Nat := healthyEntry entry + 28

def other (target : Channel n) : Nat := if target.val = 0 then 1 else 0

def tailCode (b : Nat) (target : Channel n) (nodes base entry none keep single : Nat) : List (Instruction width 8) :=
  if b = 1 then readCode (base + (n - target.val) * nodes) keep none 0
  else callCode positiveTest n nodes base 0 n entry keep (entry + 21) ++
    callCode freeTest n nodes base 0 n (entry + 21) single none

def code (b : Nat) (target : Channel n) (nodes base entry none keep single : Nat) : List (Instruction width 8) :=
  readCode base (nonzero entry) none 0 ++
  (callCode positiveTest n nodes base 0 target.val (nonzero entry) (unhealthyEntry entry) (nonzero entry + 21) ++
  (callCode positiveTest n nodes base (target.val + 1) (n - target.val - 1) (nonzero entry + 21)
    (unhealthyEntry entry) (nonzero entry + 42) ++
  (readCode (base + (n - target.val) * nodes) (healthyEntry entry) (unhealthyEntry entry) 0 ++
  (callCode negativeTest n nodes base 0 n (healthyEntry entry) single (healthyEntry entry + 21) ++
  (readCode (base + n * nodes + (n - target.val) * nodes) none
    (if b ≠ 1 ∧ 2 ≤ n then single else none) (other target) ++
  (callCode conflictTest n nodes base 0 n (unhealthyEntry entry) none (unhealthyEntry entry + 22) ++
  tailCode b target nodes base (unhealthyEntry entry + 22) none keep single))))))

theorem code_prefix_length (b : Nat) (target : Channel n) (nodes base entry none keep single : Nat) :
    entry + (code (width := width) b target nodes base entry none keep single).length =
      unhealthyEntry entry + 22 + (tailCode (width := width) b target nodes base (unhealthyEntry entry + 22) none keep single).length := by
  simp [code, unhealthyEntry, healthyEntry, nonzero, positiveTest, negativeTest, conflictTest]
  omega

theorem tailCode_length_le (b : Nat) (target : Channel n) (nodes base entry none keep single : Nat) :
    (tailCode (width := width) b target nodes base entry none keep single).length ≤ 42 := by
  unfold tailCode; split <;> simp [positiveTest, freeTest]

/-- Where the routine leaves for each decision. -/
def Lands (none keep single : Nat) (s : State width 8) : Option (Descriptor n) → Prop
  | Option.none => s.pc = word width none
  | some .keep => s.pc = word width keep
  | some (.single c) => s.pc = word width single ∧ s.reg 1 = word width c.val

set_option maxHeartbeats 8000000 in
theorem execution (graph : DAG n) (noOr : GateBasis.NoDisjunction graph) (program : Program width 8)
    (b : Nat) (target : Channel n) (base entry none keep single : Nat) (root : Fin graph.nodeCount)
    (state : State width 8) (position : state.pc = word width entry) (running : state.halted = false)
    (room : base + (2 * n + 1) * graph.nodeCount + entry + 200 < 2 ^ width)
    (rootReg : state.reg 4 = word width root.val) (stored : MatrixAt state.heap base graph)
    (present : SharedRootRead.BlockAt program entry (code b target graph.nodeCount base entry none keep single)) :
    ∃ final, Quiet program state final (64 * n + 64) ∧
      Lands none keep single final (decision b target (LiteralMachine.summary graph root)) := by
  have rootBound := root.isLt
  have targetBound := target.isLt
  have nLe : n ≤ n * graph.nodeCount := Nat.le_mul_of_pos_right _ (by omega)
  have big : (2 * n + 1) * graph.nodeCount = n * graph.nodeCount + n * graph.nodeCount + graph.nodeCount := by
    rw [Nat.add_mul, Nat.one_mul, Nat.two_mul, Nat.add_mul]
  have targetLe : (n - target.val) * graph.nodeCount ≤ n * graph.nodeCount := Nat.mul_le_mul_right _ (by omega)
  have fourRoom : 4 < 2 ^ width := by omega
  -- Code blocks.
  unfold code at present
  have zeroAt := SharedDetectorAssembly.block_left program _ _ _ present
  have r1 := SharedDetectorAssembly.block_right program _ _ _ present
  have lowAt := SharedDetectorAssembly.block_left program _ _ _ r1
  have r2 := SharedDetectorAssembly.block_right program _ _ _ r1
  have highAt := SharedDetectorAssembly.block_left program _ _ _ r2
  have r3 := SharedDetectorAssembly.block_right program _ _ _ r2
  have negTAt := SharedDetectorAssembly.block_left program _ _ _ r3
  have r4 := SharedDetectorAssembly.block_right program _ _ _ r3
  have negAt := SharedDetectorAssembly.block_left program _ _ _ r4
  have r5 := SharedDetectorAssembly.block_right program _ _ _ r4
  have posTAt := SharedDetectorAssembly.block_left program _ _ _ r5
  have r6 := SharedDetectorAssembly.block_right program _ _ _ r5
  have conflictAt := SharedDetectorAssembly.block_left program _ _ _ r6
  have tailAt := SharedDetectorAssembly.block_right program _ _ _ r6
  simp only [readCode_length, callCode_length, positiveTest, negativeTest, conflictTest, List.length_cons,
    List.length_nil] at lowAt highAt negTAt negAt posTAt conflictAt tailAt
  have lowAt' := SharedDetectorAssembly.block_move program lowAt (show entry + 7 = nonzero entry from rfl)
  have highAt' := SharedDetectorAssembly.block_move program highAt
    (show entry + 7 + (0 + 1 + 1 + 19) = nonzero entry + 21 by simp [nonzero])
  have negTAt' := SharedDetectorAssembly.block_move program negTAt
    (show entry + 7 + (0 + 1 + 1 + 19) + (0 + 1 + 1 + 19) = nonzero entry + 42 by simp [nonzero])
  have negAt' := SharedDetectorAssembly.block_move program negAt
    (show entry + 7 + (0 + 1 + 1 + 19) + (0 + 1 + 1 + 19) + 7 = healthyEntry entry by simp [healthyEntry, nonzero])
  have posTAt' := SharedDetectorAssembly.block_move program posTAt
    (show entry + 7 + (0 + 1 + 1 + 19) + (0 + 1 + 1 + 19) + 7 + (0 + 1 + 1 + 19) = healthyEntry entry + 21 by
      simp [healthyEntry, nonzero])
  have conflictAt' := SharedDetectorAssembly.block_move program conflictAt
    (show entry + 7 + (0 + 1 + 1 + 19) + (0 + 1 + 1 + 19) + 7 + (0 + 1 + 1 + 19) + 7 = unhealthyEntry entry by
      simp [unhealthyEntry, healthyEntry, nonzero])
  have tailAt' := SharedDetectorAssembly.block_move program tailAt
    (show entry + 7 + (0 + 1 + 1 + 19) + (0 + 1 + 1 + 19) + 7 + (0 + 1 + 1 + 19) + 7 + (0 + 1 + 1 + 1 + 19) =
      unhealthyEntry entry + 22 by simp [unhealthyEntry, healthyEntry, nonzero])
  set a := LiteralMachine.summary graph root with aDef
  -- Cells.
  have zeroCell := zero_cell_at graph noOr state.heap base stored root
  have negTCell := neg_cell graph noOr state.heap base stored target root
  have posTCell := pos_cell graph noOr state.heap base stored target root
  -- The unhealthy branch.
  have unhealthy : ∀ s : State width 8, s.pc = word width (unhealthyEntry entry) → s.halted = false →
      s.heap = state.heap → s.reg 4 = state.reg 4 →
      ∃ final, Quiet program s final (48 * n + 32) ∧
        Lands none keep single final
          (if (firstHit (fun c => posBit a c && negBit a c) 0 n).isSome || (b == 1 && negBit a target.val) then Option.none
          else if b = 1 ∨ (firstHit (posBit a) 0 n).isSome then some .keep
          else (toChannel (n := n) (firstHit (fun c => !negBit a c) 0 n)).map .single) := by
    intro s spc srun sheap sreg
    have sRoot : s.reg 4 = word width root.val := sreg.trans rootReg
    have sStored : MatrixAt s.heap base graph := by rw [sheap]; exact stored
    obtain ⟨c1, q1, l1⟩ := call_quiet graph noOr program conflictTest 3 (fun _ p q => p && q) (conflict_spec fourRoom)
      base 0 n (unhealthyEntry entry) none (unhealthyEntry entry + 22) root s spc srun (by omega)
      (by simp [conflictTest, unhealthyEntry, healthyEntry, nonzero]; omega) sRoot sStored conflictAt'
    have l1' : match firstHit (fun c => posBit a c && negBit a c) 0 n with
        | some d => c1.pc = word width none ∧ c1.reg 1 = word width d
        | Option.none => c1.pc = word width (unhealthyEntry entry + 22) := l1
    cases hc : firstHit (fun c => posBit a c && negBit a c) 0 n with
    | some d =>
      rw [hc] at l1'
      refine ⟨c1, q1.mono (by omega), ?_⟩
      simp only [Option.isSome_some, Bool.true_or, ite_true]
      exact l1'.1
    | none =>
      rw [hc] at l1'
      obtain ⟨_, _, _, crun, cheap, _, _, creg⟩ := id q1
      have cRoot : c1.reg 4 = word width root.val := by rw [creg, sRoot]
      have cStored : MatrixAt c1.heap base graph := by rw [cheap]; exact sStored
      simp only [Option.isSome_none, Bool.false_or]
      by_cases one : b = 1
      · simp only [tailCode, one, ite_true] at tailAt'
        obtain ⟨c2, q2, l2⟩ := read_quiet program c1 (unhealthyEntry entry + 22) (base + (n - target.val) * graph.nodeCount)
          keep none 0 root.val (negBit a target.val) l1' crun
          (by simp [unhealthyEntry, healthyEntry, nonzero]; omega) cRoot
          (by rw [cheap, sheap]; exact negTCell) tailAt'
        refine ⟨c2, (q1.trans q2).mono (by omega), ?_⟩
        cases hn : negBit a target.val
        · simp only [hn] at l2; simpa [one, hn, Lands] using l2
        · simp only [hn, ite_true] at l2; simpa [one, hn, Lands] using l2.1
      · simp only [tailCode, one, ite_false] at tailAt'
        have posAt := SharedDetectorAssembly.block_left program _ _ _ tailAt'
        have freeAt := SharedDetectorAssembly.block_right program _ _ _ tailAt'
        simp only [callCode_length, positiveTest, List.length_cons, List.length_nil] at freeAt
        obtain ⟨c2, q2, l2⟩ := call_quiet graph noOr program positiveTest 2 (fun _ p _ => p) (positive_spec fourRoom)
          base 0 n (unhealthyEntry entry + 22) keep (unhealthyEntry entry + 22 + 21) root c1 l1' crun (by omega)
          (by simp [positiveTest, unhealthyEntry, healthyEntry, nonzero]; omega) cRoot cStored posAt
        have l2' : match firstHit (posBit a) 0 n with
            | some d => c2.pc = word width keep ∧ c2.reg 1 = word width d
            | Option.none => c2.pc = word width (unhealthyEntry entry + 22 + 21) := l2
        cases hp : firstHit (posBit a) 0 n with
        | some d =>
          rw [hp] at l2'
          refine ⟨c2, (q1.trans q2).mono (by omega), ?_⟩
          simpa [one, hp, Lands] using l2'.1
        | none =>
          rw [hp] at l2'
          obtain ⟨_, _, _, crun2, cheap2, _, _, creg2⟩ := id q2
          obtain ⟨c3, q3, l3⟩ := call_quiet graph noOr program freeTest 2 (fun _ _ q => !q) (free_spec fourRoom)
            base 0 n (unhealthyEntry entry + 22 + 21) single none root c2 l2' crun2 (by omega)
            (by simp [freeTest, unhealthyEntry, healthyEntry, nonzero]; omega) (by rw [creg2, cRoot])
            (by rw [cheap2]; exact cStored) (by simpa [Nat.add_assoc] using freeAt)
          have l3' : match firstHit (fun c => !negBit a c) 0 n with
              | some d => c3.pc = word width single ∧ c3.reg 1 = word width d
              | Option.none => c3.pc = word width none := l3
          refine ⟨c3, ((q1.trans q2).trans q3).mono (by omega), ?_⟩
          cases hf : firstHit (fun c => !negBit a c) 0 n with
          | none => rw [hf] at l3'; simpa [toChannel, one, hp, Lands] using l3'
          | some d =>
            rw [hf] at l3'
            have dBound : d < n := by have := firstHit_bound _ 0 n d hf; omega
            simpa [toChannel, dBound, Lands, one, hp] using l3'
  -- The healthy branch.
  have healthy : ∀ s : State width 8, s.pc = word width (healthyEntry entry) → s.halted = false →
      s.heap = state.heap → s.reg 4 = state.reg 4 →
      ∃ final, Quiet program s final (16 * n + 20) ∧
        Lands none keep single final
          (match toChannel (n := n) (firstHit (negBit a) 0 n) with
            | some m => some (.single m)
            | Option.none =>
              if room : b ≠ 1 ∧ posBit a target.val = true ∧ 2 ≤ n then
                some (.single ⟨if target.val = 0 then 1 else 0, by have := room.2.2; split <;> omega⟩)
              else Option.none) := by
    intro s spc srun sheap sreg
    have sRoot : s.reg 4 = word width root.val := sreg.trans rootReg
    have sStored : MatrixAt s.heap base graph := by rw [sheap]; exact stored
    obtain ⟨c1, q1, l1⟩ := call_quiet graph noOr program negativeTest 2 (fun _ _ q => q) (negative_spec fourRoom)
      base 0 n (healthyEntry entry) single (healthyEntry entry + 21) root s spc srun (by omega)
      (by simp [negativeTest, unhealthyEntry, healthyEntry, nonzero]; omega) sRoot sStored negAt'
    have l1' : match firstHit (negBit a) 0 n with
        | some d => c1.pc = word width single ∧ c1.reg 1 = word width d
        | Option.none => c1.pc = word width (healthyEntry entry + 21) := l1
    cases hm : firstHit (negBit a) 0 n with
    | some d =>
      rw [hm] at l1'
      have dBound : d < n := by have := firstHit_bound _ 0 n d hm; omega
      exact ⟨c1, q1.mono (by omega), by simpa [toChannel, dBound, Lands] using l1'⟩
    | none =>
      rw [hm] at l1'
      obtain ⟨_, _, _, crun, cheap, _, _, creg⟩ := id q1
      obtain ⟨c2, q2, l2⟩ := read_quiet program c1 (healthyEntry entry + 21)
        (base + n * graph.nodeCount + (n - target.val) * graph.nodeCount) none
        (if b ≠ 1 ∧ 2 ≤ n then single else none) (other target) root.val (posBit a target.val) l1' crun
        (by simp [other, unhealthyEntry, healthyEntry, nonzero]; split <;> omega) (by rw [creg, sRoot])
        (by rw [cheap, sheap]; exact posTCell) posTAt'
      refine ⟨c2, (q1.trans q2).mono (by omega), ?_⟩
      simp only [toChannel]
      by_cases hp : posBit a target.val = true
      · simp only [hp, ite_true] at l2
        by_cases room : b ≠ 1 ∧ 2 ≤ n
        · simp only [room, and_self, ite_true] at l2
          have cond : b ≠ 1 ∧ posBit a target.val = true ∧ 2 ≤ n := ⟨room.1, hp, room.2⟩
          rw [dite_eq_left cond]
          simpa [Lands, other, room.1] using l2
        · simp only [room, ite_false] at l2
          have cond : ¬(b ≠ 1 ∧ posBit a target.val = true ∧ 2 ≤ n) := fun h => room ⟨h.1, h.2.2⟩
          rw [dite_eq_right cond]
          exact l2.1
      · have hf : posBit a target.val = false := by simpa using hp
        simp only [hf] at l2
        have cond : ¬(b ≠ 1 ∧ posBit a target.val = true ∧ 2 ≤ n) := fun h => hp h.2.1
        rw [dite_eq_right cond]
        exact l2
  -- The common prefix.
  obtain ⟨z1, qz, lz⟩ := read_quiet program state entry base (nonzero entry) none 0 root.val a.zero position running
    (by omega) rootReg zeroCell zeroAt
  have decisionUnhealthy : ∀ (notHealthy : (!a.zero && (firstHit (posBit a) 0 target.val).isNone &&
      (firstHit (posBit a) (target.val + 1) (n - target.val - 1)).isNone && !negBit a target.val) = false)
      (zero : a.zero = false),
      decision b target a =
        (if (firstHit (fun c => posBit a c && negBit a c) 0 n).isSome || (b == 1 && negBit a target.val) then Option.none
          else if b = 1 ∨ (firstHit (posBit a) 0 n).isSome then some .keep
          else (toChannel (n := n) (firstHit (fun c => !negBit a c) 0 n)).map .single) := by
    intro notHealthy zero
    unfold decision
    dsimp only
    rw [ite_eq_right (by simp [notHealthy]), ite_eq_right (by simp [zero])]
  cases hz : a.zero
  · simp only [hz] at lz
    obtain ⟨_, _, _, zrun, zheap, _, _, zreg⟩ := id qz
    obtain ⟨c1, q1, l1⟩ := call_quiet graph noOr program positiveTest 2 (fun _ p _ => p) (positive_spec fourRoom)
      base 0 target.val (nonzero entry) (unhealthyEntry entry) (nonzero entry + 21) root z1 lz zrun (by omega)
      (by simp [positiveTest, unhealthyEntry, healthyEntry, nonzero]; omega) (by rw [zreg, rootReg])
      (by rw [zheap]; exact stored) lowAt'
    have l1' : match firstHit (posBit a) 0 target.val with
        | some d => c1.pc = word width (unhealthyEntry entry) ∧ c1.reg 1 = word width d
        | Option.none => c1.pc = word width (nonzero entry + 21) := l1
    obtain ⟨_, _, _, crun, cheap, _, _, creg⟩ := id q1
    cases hl : firstHit (posBit a) 0 target.val with
    | some d =>
      rw [hl] at l1'
      obtain ⟨u, qu, lu⟩ := unhealthy c1 l1'.1 crun (by rw [cheap, zheap]) (by rw [creg, zreg])
      refine ⟨u, ((qz.trans q1).trans qu).mono (by omega), ?_⟩
      rw [decisionUnhealthy (by simp [hl]) hz]
      exact lu
    | none =>
      rw [hl] at l1'
      obtain ⟨c2, q2, l2⟩ := call_quiet graph noOr program positiveTest 2 (fun _ p _ => p) (positive_spec fourRoom)
        base (target.val + 1) (n - target.val - 1) (nonzero entry + 21) (unhealthyEntry entry) (nonzero entry + 42)
        root c1 l1' crun (by omega)
        (by simp [positiveTest, unhealthyEntry, healthyEntry, nonzero]; omega) (by rw [creg, zreg, rootReg])
        (by rw [cheap, zheap]; exact stored) highAt'
      have l2' : match firstHit (posBit a) (target.val + 1) (n - target.val - 1) with
          | some d => c2.pc = word width (unhealthyEntry entry) ∧ c2.reg 1 = word width d
          | Option.none => c2.pc = word width (nonzero entry + 42) := l2
      obtain ⟨_, _, _, crun2, cheap2, _, _, creg2⟩ := id q2
      have counts : target.val * (2 + 13) + 7 + ((n - target.val - 1) * (2 + 13) + 7) ≤ 15 * n + 14 := by
        have := Nat.add_mul target.val (n - target.val - 1) 15
        have : target.val + (n - target.val - 1) ≤ n := by omega
        have := Nat.mul_le_mul_right 15 this
        omega
      cases hh : firstHit (posBit a) (target.val + 1) (n - target.val - 1) with
      | some d =>
        rw [hh] at l2'
        obtain ⟨u, qu, lu⟩ := unhealthy c2 l2'.1 crun2 (by rw [cheap2, cheap, zheap]) (by rw [creg2, creg, zreg])
        refine ⟨u, (((qz.trans q1).trans q2).trans qu).mono (by omega), ?_⟩
        rw [decisionUnhealthy (by simp [hl, hh]) hz]
        exact lu
      | none =>
        rw [hh] at l2'
        obtain ⟨c3, q3, l3⟩ := read_quiet program c2 (nonzero entry + 42) (base + (n - target.val) * graph.nodeCount)
          (healthyEntry entry) (unhealthyEntry entry) 0 root.val (negBit a target.val) l2' crun2
          (by simp [unhealthyEntry, healthyEntry, nonzero]; omega) (by rw [creg2, creg, zreg, rootReg])
          (by rw [cheap2, cheap, zheap]; exact negTCell) negTAt'
        obtain ⟨_, _, _, crun3, cheap3, _, _, creg3⟩ := id q3
        cases hn : negBit a target.val
        · simp only [hn] at l3
          obtain ⟨h, qh, lh⟩ := healthy c3 (by simpa [healthyEntry] using l3) crun3
            (by rw [cheap3, cheap2, cheap, zheap]) (by rw [creg3, creg2, creg, zreg])
          refine ⟨h, ((((qz.trans q1).trans q2).trans q3).trans qh).mono (by omega), ?_⟩
          have flag : (!a.zero && (firstHit (posBit a) 0 target.val).isNone &&
              (firstHit (posBit a) (target.val + 1) (n - target.val - 1)).isNone && !negBit a target.val) = true := by
            simp [hz, hl, hh, hn]
          unfold decision
          simp only [flag, ite_true]
          exact lh
        · simp only [hn, ite_true] at l3
          obtain ⟨u, qu, lu⟩ := unhealthy c3 l3.1 crun3 (by rw [cheap3, cheap2, cheap, zheap])
            (by rw [creg3, creg2, creg, zreg])
          refine ⟨u, ((((qz.trans q1).trans q2).trans q3).trans qu).mono (by omega), ?_⟩
          rw [decisionUnhealthy (by simp [hn]) hz]
          exact lu
  · simp only [hz, ite_true] at lz
    refine ⟨z1, qz.mono (by omega), ?_⟩
    have : decision b target a = Option.none := by
      unfold decision; simp [hz]
    rw [this]
    exact lz.1

end Controller.Extensions.LiteralRootRun

