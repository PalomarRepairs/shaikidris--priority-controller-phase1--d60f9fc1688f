module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.MonotoneRoot

@[expose] public section

/-! A monotone root decision followed by the actual channel vector. -/
namespace Controller.Extensions.MonotoneReturn
open Controller.Decoder Controller.Cost Controller.Extensions.MonotoneDecision
open Controller.Extensions.LiteralWitnessEmit
open Controller.Extensions.LiteralScan (word_val)
open Controller.Extensions.LiteralWitnessReturn (words jump)

variable {n width : Nat}

def operands (full : Bool) (n : Nat) : List Operand :=
  (List.finRange n).reverse.map (fun c => if full then .one else .selected c.val)

@[simp] theorem operands_length (full : Bool) (n : Nat) : (operands full n).length = n := by simp [operands]

def fullMode : Descriptor n → Bool
  | .full => true | .single _ => false

def Selected (state : State width 8) : Descriptor n → Prop
  | .full => True | .single c => state.reg 1 = word width c.val

theorem descriptor_execution (program : Program width 8) (state : State width 8) (entry : Nat) (d : Descriptor n)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 9 * n < 2 ^ width) (channelFits : n < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (selected : Selected state d)
    (present : SharedRootRead.BlockAt program entry (LiteralWitnessEmit.code entry (operands (fullMode d) n))) :
    ∃ final, Emits program state final (9 * n) (words width d.set) ∧
      final.pc = word width (entry + size (operands (fullMode d) n)) := by
  have same (i : Fin 8) : state.reg i = word width (state.reg i).val := by
    apply Fin.ext; exact (word_val _ (state.reg i).isLt).symm
  have bound := size_bound (operands (fullMode d) n)
  rw [operands_length] at bound
  obtain ⟨final, trace, pc⟩ := LiteralWitnessEmit.execution program (operands (fullMode d) n)
    (state.reg 4).val (state.reg 1).val entry state position running (by omega) heapFits (state.reg 1).isLt
    (same 4) (same 1)
    (by
      intro op member
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp member
      cases d with
      | full => trivial
      | single d => exact c.isLt.trans channelFits) present
  have output : ((operands (fullMode d) n).map (operandValue state.heap (state.reg 4).val (state.reg 1).val)).reverse =
      words width d.set := by
    simp only [operands, List.map_map, ← List.map_reverse, List.reverse_reverse, words]
    apply List.map_congr_left
    intro c _
    cases d with
    | full => simp [fullMode, operandValue, Descriptor.set]
    | single d =>
      have reg : (state.reg 1).val = d.val := by rw [selected]; exact word_val _ (d.isLt.trans channelFits)
      have eq : d.val = c.val ↔ c = d := ⟨fun h => (Fin.ext h).symm, fun h => by rw [h]⟩
      simp [fullMode, operandValue, Descriptor.set, reg, eq]
  rw [operands_length, output] at trace
  exact ⟨final, trace, pc⟩

def rootSize (b : Nat) : Nat := 14 + if b = 1 then 2 else 19
def fullEntry (b entry : Nat) : Nat := entry + rootSize b
def singleEntry (b n entry : Nat) : Nat := fullEntry b entry + size (operands true n) + 2
def finish (b n entry : Nat) : Nat := singleEntry b n entry + size (operands false n)

def code (b : Nat) (target : Channel n) (nodes base entry absent : Nat) : List (Instruction width 8) :=
  MonotoneRoot.code b target nodes base entry absent (fullEntry b entry) (singleEntry b n entry) ++
    (LiteralWitnessEmit.code (fullEntry b entry) (operands true n) ++
      (jump (finish b n entry) ++ LiteralWitnessEmit.code (singleEntry b n entry) (operands false n)))

theorem code_length (b : Nat) (target : Channel n) (nodes base entry absent : Nat) :
    entry + (code (width := width) b target nodes base entry absent).length = finish b n entry := by
  simp only [code, List.length_append, MonotoneRoot.code_length, LiteralWitnessEmit.code_length,
    jump, List.length_cons, List.length_nil, finish, singleEntry, fullEntry, rootSize]
  omega

theorem code_length_bound (b : Nat) (target : Channel n) (nodes base entry absent : Nat) :
    (code (width := width) b target nodes base entry absent).length ≤ 35 + 18 * n := by
  have root : rootSize b ≤ 33 := by unfold rootSize; split <;> omega
  have full := size_bound (operands true n)
  have single := size_bound (operands false n)
  simp only [operands_length] at full single
  have length := code_length (width := width) b target nodes base entry absent
  unfold finish singleEntry fullEntry at length
  omega

def Result (absent done : Nat) (before after : State width 8) : Option (Descriptor n) → Prop
  | none => after.pc = word width absent ∧ after.output = before.output
  | some d => after.pc = word width done ∧ after.output = words width d.set ++ before.output

theorem execution (program : Program width 8) (state : State width 8) (graph : DAG n)
    (b : Nat) (target : Channel n) (base entry absent : Nat) (root : Fin graph.nodeCount)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : base + (n + 1) * graph.nodeCount + entry + 18 * n + 128 < 2 ^ width)
    (heapFits : state.heap.size < 2 ^ width) (held : state.reg 4 = word width root.val)
    (stored : MonotoneRoot.MatrixAt state.heap base graph)
    (present : SharedRootRead.BlockAt program entry (code b target graph.nodeCount base entry absent)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧ ticks ≤ 22 * n + 18 ∧
      peak ≤ state.liveWords + n ∧ final.heap = state.heap ∧ final.stack = state.stack ∧ final.halted = false ∧
      Result absent (finish b n entry) state final (decision graph b target root) := by
  have rootBound : rootSize b ≤ 33 := by unfold rootSize; split <;> omega
  have fb := size_bound (operands true n)
  have sb := size_bound (operands false n)
  simp only [operands_length] at fb sb
  have rootAt := SharedDetectorAssembly.block_left program entry _ _ present
  have tailAt := SharedDetectorAssembly.block_right program entry _ _ present
  rw [MonotoneRoot.code_length] at tailAt
  have fullAt := SharedDetectorAssembly.block_left program (fullEntry b entry) _ _ tailAt
  have restAt := SharedDetectorAssembly.block_right program (fullEntry b entry) _ _ tailAt
  rw [LiteralWitnessEmit.code_length] at restAt
  have jumpAt := SharedDetectorAssembly.block_left program _ _ _ restAt
  have singleAt := SharedDetectorAssembly.block_right program _ _ _ restAt
  simp only [jump, List.length_cons, List.length_nil, Nat.reduceAdd] at singleAt
  obtain ⟨middle, quiet, lands⟩ := MonotoneRoot.execution program graph b target base entry absent
    (fullEntry b entry) (singleEntry b n entry) root state position running (by omega) held stored rootAt
  obtain ⟨t, trace, time, active, heap, stack, output, frame⟩ := quiet
  have live : middle.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  cases choice : decision graph b target root with
  | none =>
    exact ⟨middle, t, state.liveWords, trace, by omega, by omega, heap, stack, active,
      by simpa only [choice, MonotoneRoot.Lands, Result] using And.intro lands output⟩
  | some descriptor =>
    cases descriptor with
    | full =>
      have pc : middle.pc = word width (fullEntry b entry) := by simpa [choice, MonotoneRoot.Lands] using lands
      obtain ⟨emitted, emission, endPC⟩ := descriptor_execution program middle (fullEntry b entry) (.full : Descriptor n)
        pc active (by dsimp [fullEntry]; omega) (by omega) (by rw [heap]; exact heapFits) trivial fullAt
      have emittedLive := emission.live
      obtain ⟨u, tr, ub, h, s, o, run, _, _⟩ := emission
      obtain ⟨final, jumpTrace, pc, hf, sf, of, rf, _⟩ := EnumerationSteps.jump_execution program emitted
        (fullEntry b entry + size (operands true n)) (finish b n entry) endPC run (by dsimp [fullEntry]; omega)
        (by simpa [jump] using jumpAt 0 (by simp [jump]))
        (by simpa [jump] using jumpAt 1 (by simp [jump]))
      refine ⟨final, t + u + 2, state.liveWords + n, ?_, by omega, le_rfl,
        hf.trans (h.trans heap), sf.trans (s.trans stack), rf, ?_⟩
      · simpa only [LiteralWitnessReturn.words_length, live, emittedLive,
          Nat.max_eq_right (Nat.le_add_right _ _), Nat.max_self] using (trace.append tr).append jumpTrace
      · exact ⟨pc, by rw [of, o, output]⟩
    | single c =>
      have landed : middle.pc = word width (singleEntry b n entry) ∧ middle.reg 1 = word width c.val := by
        simpa [choice, MonotoneRoot.Lands] using lands
      obtain ⟨final, emission, pc⟩ := descriptor_execution program middle (singleEntry b n entry) (.single c)
        landed.1 active (by dsimp [singleEntry, fullEntry]; omega) (by omega)
        (by rw [heap]; exact heapFits) landed.2 singleAt
      obtain ⟨u, tr, ub, h, s, o, run, _, _⟩ := emission
      refine ⟨final, t + u, state.liveWords + n, ?_, by omega, le_rfl, h.trans heap, s.trans stack, run, ?_⟩
      · simpa only [LiteralWitnessReturn.words_length, live, Nat.max_eq_right (Nat.le_add_right _ _)] using trace.append tr
      · exact ⟨pc, by rw [o, output]⟩

end Controller.Extensions.MonotoneReturn
