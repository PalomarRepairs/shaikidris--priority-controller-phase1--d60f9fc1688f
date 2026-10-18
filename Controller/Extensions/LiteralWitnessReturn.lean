module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralWitnessEmit

@[expose] public section

/-! Physical witness output for the no-OR decision. Each instruction sequence
depends on the matrix dimensions, bus count, target and descriptor mode. The
root, selected channel and positive-literal bits are read at runtime. -/
namespace Controller.Extensions.LiteralWitnessReturn
open Controller.Decoder Controller.Cost Controller.Extensions.LiteralDecision
open Controller.Extensions.LiteralRoot Controller.Extensions.LiteralWitnessEmit
open Controller.Extensions.LiteralWitness (forced)
open Controller.Extensions.LiteralScan (word_val)

variable {n width : Nat}

def keepMode : Descriptor n → Bool
  | .keep => true | .single _ => false

def operand (keep : Bool) (b : Nat) (target : Channel n) (nodes base : Nat) (c : Channel n) : Operand :=
  if b = 1 ∧ c = target then .one
  else if keep then .stored (base + n * nodes + (n - c.val) * nodes) else .selected c.val

def operands (keep : Bool) (b : Nat) (target : Channel n) (nodes base : Nat) : List Operand :=
  (List.finRange n).reverse.map (operand keep b target nodes base)

@[simp] theorem operands_length (keep : Bool) (b : Nat) (target : Channel n) (nodes base : Nat) :
    (operands keep b target nodes base).length = n := by simp [operands]

def words (width : Nat) (K : Finset (Channel n)) : List (Word width) :=
  (List.finRange n).map (fun c => boolWord width (decide (c ∈ K)))

@[simp] theorem words_length (K : Finset (Channel n)) : (words width K).length = n := by simp [words]

def Selected (state : State width 8) : Descriptor n → Prop
  | .keep => True
  | .single c => state.reg 1 = word width c.val

theorem forced_mem (b : Nat) (target c : Channel n) : c ∈ forced b target ↔ b = 1 ∧ c = target := by
  by_cases h : b = 1 <;> simp [forced, h]

theorem operand_valid (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (heap : Array (Word width)) (base : Nat) (root : Fin graph.nodeCount)
    (stored : MatrixAt heap base graph) (keep : Bool) (b : Nat) (target c : Channel n)
    (channelFits : n < 2 ^ width) : Valid heap root.val (operand keep b target graph.nodeCount base c) := by
  unfold operand
  split
  · trivial
  · split
    · exact (Array.getElem?_eq_some_iff.mp (pos_cell graph noOr heap base stored c root)).1
    · exact c.isLt.trans channelFits

theorem operand_value (graph : DAG n) (noOr : GateBasis.NoDisjunction graph) (state : State width 8)
    (base : Nat) (root : Fin graph.nodeCount) (stored : MatrixAt state.heap base graph)
    (b : Nat) (target c : Channel n) (descriptor : Descriptor n) (selected : Selected state descriptor)
    (channelFits : n < 2 ^ width) :
    operandValue state.heap root.val (state.reg 1).val (operand (keepMode descriptor) b target graph.nodeCount base c) =
      boolWord width (decide (c ∈ descriptor.set b target (LiteralMachine.summary graph root))) := by
  have positive := pos_cell graph noOr state.heap base stored c root
  have valid := (Array.getElem?_eq_some_iff.mp positive).1
  have loaded : EnumerationStreamEmit.heapValue state.heap
      (base + n * graph.nodeCount + (n - c.val) * graph.nodeCount + root.val) =
      boolWord width (decide (c ∈ (LiteralMachine.summary graph root).positive)) := by
    rw [EnumerationStreamEmit.heapValue_eq _ _ valid]
    simpa only [posBit_channel] using (Array.getElem?_eq_some_iff.mp positive).2
  have same (d : Channel n) : d.val = c.val ↔ c = d := by
    exact ⟨fun h => (Fin.ext h).symm, fun h => by rw [h]⟩
  cases descriptor with
  | keep =>
    by_cases force : b = 1 ∧ c = target
    · simp [operand, force, operandValue, Descriptor.set, forced_mem]
    · simpa [operand, force, keepMode, operandValue, Descriptor.set, forced_mem] using loaded
  | single d =>
    have reg : (state.reg 1).val = d.val := by rw [selected]; exact word_val _ (d.isLt.trans channelFits)
    by_cases force : b = 1 ∧ c = target <;>
      simp [operand, force, keepMode, operandValue, Descriptor.set, forced_mem, reg, same]

theorem descriptor_execution (program : Program width 8) (state : State width 8)
    (graph : DAG n) (noOr : GateBasis.NoDisjunction graph) (b : Nat) (target : Channel n)
    (base entry : Nat) (root : Fin graph.nodeCount) (descriptor : Descriptor n)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 9 * n < 2 ^ width) (channelFits : n < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (rootReg : state.reg 4 = word width root.val)
    (stored : MatrixAt state.heap base graph) (selected : Selected state descriptor)
    (present : SharedRootRead.BlockAt program entry
      (LiteralWitnessEmit.code entry (operands (keepMode descriptor) b target graph.nodeCount base))) :
    ∃ final, Emits program state final (9 * n) (words width (descriptor.set b target (LiteralMachine.summary graph root))) ∧
      final.pc = word width (entry + size (operands (keepMode descriptor) b target graph.nodeCount base)) := by
  have bound := size_bound (operands (keepMode descriptor) b target graph.nodeCount base)
  rw [operands_length] at bound
  have r1 : state.reg 1 = word width (state.reg 1).val := by
    apply Fin.ext
    exact (word_val _ (state.reg 1).isLt).symm
  obtain ⟨final, trace, pc⟩ := LiteralWitnessEmit.execution program
    (operands (keepMode descriptor) b target graph.nodeCount base) root.val (state.reg 1).val entry state
    position running (by omega) heapFits (state.reg 1).isLt rootReg r1
    (by
      intro op member
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp member
      exact operand_valid graph noOr state.heap base root stored _ b target c channelFits) present
  have output : ((operands (keepMode descriptor) b target graph.nodeCount base).map
      (operandValue state.heap root.val (state.reg 1).val)).reverse =
      words width (descriptor.set b target (LiteralMachine.summary graph root)) := by
    simp only [operands, List.map_map, ← List.map_reverse, List.reverse_reverse, words]
    apply List.map_congr_left
    intro c _
    exact operand_value graph noOr state base root stored b target c descriptor selected channelFits
  rw [operands_length, output] at trace
  exact ⟨final, trace, pc⟩

def rootSize (b : Nat) : Nat := 106 + if b = 1 then 7 else 42

theorem root_code_length (b : Nat) (target : Channel n) (nodes base entry absent keep single : Nat) :
    (LiteralRootRun.code (width := width) b target nodes base entry absent keep single).length = rootSize b := by
  simp only [LiteralRootRun.code, List.length_append, LiteralRootRun.readCode_length, callCode_length]
  simp [LiteralRootRun.tailCode, rootSize, LiteralTests.positiveTest, LiteralTests.negativeTest,
    LiteralTests.conflictTest, LiteralTests.freeTest]
  split <;> simp [LiteralRootRun.readCode, callCode, LiteralScan.code, LiteralScan.head, LiteralScan.advance]

def keepEntry (b entry : Nat) : Nat := entry + rootSize b
def singleEntry (b : Nat) (target : Channel n) (nodes base entry : Nat) : Nat :=
  keepEntry b entry + size (operands true b target nodes base) + 2
def finish (b : Nat) (target : Channel n) (nodes base entry : Nat) : Nat :=
  singleEntry b target nodes base entry + size (operands false b target nodes base)

def jump (destination : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width 0), .branchZero 0 (word width destination)]

def code (b : Nat) (target : Channel n) (nodes base entry absent : Nat) : List (Instruction width 8) :=
  LiteralRootRun.code b target nodes base entry absent (keepEntry b entry) (singleEntry b target nodes base entry) ++
    (LiteralWitnessEmit.code (keepEntry b entry) (operands true b target nodes base) ++
    (jump (finish b target nodes base entry) ++
      LiteralWitnessEmit.code (singleEntry b target nodes base entry) (operands false b target nodes base)))

theorem code_length (b : Nat) (target : Channel n) (nodes base entry absent : Nat) :
    entry + (code (width := width) b target nodes base entry absent).length = finish b target nodes base entry := by
  simp [code, root_code_length, jump, finish, singleEntry, keepEntry, Nat.add_assoc]
  omega

theorem code_length_bound (b : Nat) (target : Channel n) (nodes base entry absent : Nat) :
    (code (width := width) b target nodes base entry absent).length ≤ 150 + 18 * n := by
  have root : rootSize b ≤ 148 := by unfold rootSize; split <;> omega
  have pos := size_bound (operands true b target nodes base)
  have neg := size_bound (operands false b target nodes base)
  simp only [operands_length] at pos neg
  simp only [code, List.length_append, root_code_length, LiteralWitnessEmit.code_length, jump,
    List.length_cons, List.length_nil]
  omega

def Result (b : Nat) (target : Channel n) (a : LiteralMachine.Raw n) (absent done : Nat)
    (before after : State width 8) : Option (Descriptor n) → Prop
  | none => after.pc = word width absent ∧ after.output = before.output
  | some d => after.pc = word width done ∧ after.output = words width (d.set b target a) ++ before.output

theorem execution (program : Program width 8) (state : State width 8)
    (graph : DAG n) (noOr : GateBasis.NoDisjunction graph) (b : Nat) (target : Channel n)
    (base entry absent : Nat) (root : Fin graph.nodeCount)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : base + (2 * n + 1) * graph.nodeCount + entry + 18 * n + 400 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (rootReg : state.reg 4 = word width root.val)
    (stored : MatrixAt state.heap base graph)
    (present : SharedRootRead.BlockAt program entry (code b target graph.nodeCount base entry absent)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ 73 * n + 66 ∧
      peak ≤ state.liveWords + n ∧ final.heap = state.heap ∧ final.stack = state.stack ∧
      final.halted = false ∧ Result b target (LiteralMachine.summary graph root) absent
        (finish b target graph.nodeCount base entry) state final
        (decision b target (LiteralMachine.summary graph root)) := by
  have rb : rootSize b ≤ 148 := by unfold rootSize; split <;> omega
  have kb := size_bound (operands true b target graph.nodeCount base)
  have sb := size_bound (operands false b target graph.nodeCount base)
  simp only [operands_length] at kb sb
  have rootAt := SharedDetectorAssembly.block_left program entry _ _ present
  have tailAt := SharedDetectorAssembly.block_right program entry _ _ present
  rw [root_code_length] at tailAt
  have keepAt := SharedDetectorAssembly.block_left program (keepEntry b entry) _ _ tailAt
  have restAt := SharedDetectorAssembly.block_right program (keepEntry b entry) _ _ tailAt
  rw [LiteralWitnessEmit.code_length] at restAt
  have jumpAt := SharedDetectorAssembly.block_left program _ _ _ restAt
  have singleAt := SharedDetectorAssembly.block_right program _ _ _ restAt
  simp only [jump, List.length_cons, List.length_nil] at singleAt
  obtain ⟨middle, quiet, lands⟩ := LiteralRootRun.execution graph noOr program b target base entry absent
    (keepEntry b entry) (singleEntry b target graph.nodeCount base entry) root state position running
    (by omega) rootReg stored rootAt
  obtain ⟨t, trace, time, active, heap, stack, output, reg4⟩ := quiet
  have live : middle.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  cases choice : decision b target (LiteralMachine.summary graph root) with
  | none =>
    exact ⟨middle, t, state.liveWords, trace, by omega, by omega, heap, stack, active,
      by simpa only [choice, LiteralRootRun.Lands, Result] using And.intro lands output⟩
  | some descriptor =>
    cases descriptor with
    | keep =>
      have midPC : middle.pc = word width (keepEntry b entry) := by simpa [choice, LiteralRootRun.Lands] using lands
      obtain ⟨emitted, emission, endPC⟩ := descriptor_execution program middle graph noOr b target base
        (keepEntry b entry) root .keep midPC active (by dsimp [keepEntry]; omega) (by omega)
        (by rw [heap]; exact heapFits) (reg4.trans rootReg) (by rw [heap]; exact stored) trivial keepAt
      have emittedLive := emission.live
      obtain ⟨u, tr, ub, h, s, o, run, _, _⟩ := emission
      obtain ⟨final, jumpTrace, pc, hf, sf, of, rf, _⟩ := EnumerationSteps.jump_execution program emitted
        (keepEntry b entry + size (operands true b target graph.nodeCount base))
        (finish b target graph.nodeCount base entry) endPC run (by dsimp [keepEntry]; omega)
        (by simpa [jump] using jumpAt 0 (by simp [jump]))
        (by simpa [jump] using jumpAt 1 (by simp [jump]))
      refine ⟨final, t + u + 2, state.liveWords + n, ?_, by omega, le_rfl,
        hf.trans (h.trans heap), sf.trans (s.trans stack), rf, ?_⟩
      · have joined := (trace.append tr).append jumpTrace
        simpa only [words_length, live, emittedLive, Nat.max_eq_right (Nat.le_add_right _ _), Nat.max_self] using joined
      · simp only [Result]
        exact ⟨pc, by rw [of, o, output]⟩
    | single channel =>
      have landed : middle.pc = word width (singleEntry b target graph.nodeCount base entry) ∧
          middle.reg 1 = word width channel.val := by simpa [choice, LiteralRootRun.Lands] using lands
      obtain ⟨final, emission, pc⟩ := descriptor_execution program middle graph noOr b target base
        (singleEntry b target graph.nodeCount base entry) root (.single channel) landed.1 active
        (by dsimp [singleEntry, keepEntry]; omega) (by omega) (by rw [heap]; exact heapFits)
        (reg4.trans rootReg) (by rw [heap]; exact stored) landed.2 singleAt
      obtain ⟨u, tr, ub, h, s, o, run, _, _⟩ := emission
      refine ⟨final, t + u, state.liveWords + n, ?_, by omega, le_rfl, h.trans heap, s.trans stack, run, ?_⟩
      · simpa only [words_length, live, Nat.max_eq_right (Nat.le_add_right _ _)] using trace.append tr
      · simp only [Result]
        exact ⟨pc, by rw [o, output]⟩

/-- The returned vector encodes an admissible witness that changes this root. -/
theorem decision_some_spec (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount) (descriptor : Descriptor n)
    (found : decision b target (LiteralMachine.summary graph root) = some descriptor) :
    Admissible b target (descriptor.set b target (LiteralMachine.summary graph root)) ∧
      graph.eval (assignmentOfSet (descriptor.set b target (LiteralMachine.summary graph root))) root ≠
        graph.eval (assignmentOfSet {target}) root := by
  have witness : LiteralWitness.rootWitness b target (LiteralMachine.summary graph root) =
      some (descriptor.set b target (LiteralMachine.summary graph root)) := by
    simpa [found] using (decision_set b target (LiteralMachine.summary graph root)).symm
  obtain ⟨eligible, flips⟩ := LiteralWitness.rootWitness_some b target _ _ witness
  rw [LiteralWitness.summary_holds graph noOr, LiteralWitness.summary_holds graph noOr] at flips
  refine ⟨eligible, ?_⟩
  cases h : graph.eval (assignmentOfSet (descriptor.set b target (LiteralMachine.summary graph root))) root <;>
    cases g : graph.eval (assignmentOfSet {target}) root <;> simp_all

theorem decision_none_spec (graph : DAG n) (noOr : GateBasis.NoDisjunction graph)
    (b : Nat) (target : Channel n) (root : Fin graph.nodeCount)
    (absent : decision b target (LiteralMachine.summary graph root) = none) :
    ¬∃ K, Admissible b target K ∧
      graph.eval (assignmentOfSet K) root ≠ graph.eval (assignmentOfSet {target}) root := by
  have witness : LiteralWitness.rootWitness b target (LiteralMachine.summary graph root) = none := by
    simpa [absent] using (decision_set b target (LiteralMachine.summary graph root)).symm
  intro ⟨K, eligible, different⟩
  apply (LiteralWitness.rootWitness_none_iff b target _).mp witness
  refine ⟨K, eligible, ?_⟩
  rw [LiteralWitness.summary_holds graph noOr, LiteralWitness.summary_holds graph noOr]
  cases h : graph.eval (assignmentOfSet K) root <;>
    cases g : graph.eval (assignmentOfSet {target}) root <;> simp_all

end Controller.Extensions.LiteralWitnessReturn
