module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestInputLoader
public import Controller.Cost.InputLoad
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Fetched count formation from a cold input header

A fixed sixteen-instruction routine reads the stored node, child-incidence,
guard-incidence and output counts at header addresses one through four. It
forms the remaining cache length in register zero and preserves registers two
and three. The header is at the cold input origin zero. Header loading and
payload loading are separate actual fetched phases.
-/
namespace Controller.Cost.ForestInputMetadata
open Controller.Cost.GateProgram

def code (width : ℕ) : Code width :=
  [.constant 0 (word width 1), .load 0 0, .copy 1 0,
    .add 0 0 0, .add 1 1 1, .add 1 1 1, .add 0 0 1,
    .constant 1 (word width 2), .load 1 1, .add 0 0 1,
    .constant 1 (word width 3), .load 1 1, .add 0 0 1,
    .constant 1 (word width 4), .load 1 1, .add 0 0 1]

@[simp] theorem code_length : (code width).length = 16 := rfl

/-- Scratch-field replacement is proof instrumentation for the actual two
written registers; all other caller fields are retained. -/
def scratchState (s : State width 4) (cursor : ℕ) (first second : Word width) : State width 4 :=
  { s with pc := word width cursor, reg := fun register => if register = 0 then first else if register = 1 then second else s.reg register }

@[simp] theorem scratch_liveWords (s : State width 4) (cursor : ℕ) (first second : Word width) :
    (scratchState s cursor first second).liveWords = s.liveWords := rfl

theorem scratch_identity (s : State width 4) (cursor : ℕ) (pc : s.pc = word width cursor) :
    scratchState s cursor (s.reg 0) (s.reg 1) = s := by
  have registers : (fun register : Fin 4 => if register = 0 then s.reg 0
      else if register = 1 then s.reg 1 else s.reg register) = s.reg := by
    funext register
    by_cases first : register = 0
    · subst register; simp
    · by_cases second : register = 1
      · subst register; simp
      · simp [first, second]
  unfold scratchState
  rw [registers, ← pc]

private theorem fetched (program : Program width 4) (s : State width 4)
    (base : ℕ) (instruction : Instruction width 4) (pc : s.pc = word width base)
    (fits : base < 2 ^ width) (entry : program[base]? = some instruction) :
    programStep program s = step instruction s := by
  unfold programStep
  rw [pc, show (word width base).val = base from Nat.mod_eq_of_lt fits, entry]
  rfl

private theorem fetched_block (program : Program width 4) (s : State width 4)
    (instructions : Code width) (base offset : ℕ)
    (pc : s.pc = word width (base + offset)) (fits : base + offset < 2 ^ width)
    (entry : program[base + offset]? = instructions[offset]?) :
    programStep program s = (instructions[offset]?).bind (fun instruction => step instruction s) := by
  unfold programStep
  rw [pc, show (word width (base + offset)).val = base + offset from Nat.mod_eq_of_lt fits, entry]
  rfl

/-- Flat source-derived intermediate states avoid runtime state-list creation. -/
def states (s : State width 4) (base nodes children guards roots : ℕ) : ℕ → State width 4
  | 0 => scratchState s base (s.reg 0) (s.reg 1)
  | 1 => scratchState s (base + 1) (word width 1) (s.reg 1)
  | 2 => scratchState s (base + 2) (word width nodes) (s.reg 1)
  | 3 => scratchState s (base + 3) (word width nodes) (word width nodes)
  | 4 => scratchState s (base + 4) (word width (2 * nodes)) (word width nodes)
  | 5 => scratchState s (base + 5) (word width (2 * nodes)) (word width (2 * nodes))
  | 6 => scratchState s (base + 6) (word width (2 * nodes)) (word width (4 * nodes))
  | 7 => scratchState s (base + 7) (word width (6 * nodes)) (word width (4 * nodes))
  | 8 => scratchState s (base + 8) (word width (6 * nodes)) (word width 2)
  | 9 => scratchState s (base + 9) (word width (6 * nodes)) (word width children)
  | 10 => scratchState s (base + 10) (word width (6 * nodes + children)) (word width children)
  | 11 => scratchState s (base + 11) (word width (6 * nodes + children)) (word width 3)
  | 12 => scratchState s (base + 12) (word width (6 * nodes + children)) (word width guards)
  | 13 => scratchState s (base + 13) (word width (6 * nodes + children + guards)) (word width guards)
  | 14 => scratchState s (base + 14) (word width (6 * nodes + children + guards)) (word width 4)
  | 15 => scratchState s (base + 15) (word width (6 * nodes + children + guards)) (word width roots)
  | _ => scratchState s (base + 16) (word width (6 * nodes + children + guards + roots)) (word width roots)

private theorem chain_execution (program : Program width 4) (history : ℕ → State width 4)
    (count peak : ℕ) (transitions : ∀ index < count,
      programStep program (history index) = some (history (index + 1)))
    (live : ∀ index ≤ count, (history index).liveWords = peak) :
    Execution program (history 0) (history count) count peak := by
  induction count generalizing history with
  | zero => simpa only [live 0 (le_refl _)] using Execution.refl (p := program) (history 0)
  | succ count ih =>
      have later := ih (fun index => history (index + 1))
        (fun index bound => transitions (index + 1) (by omega))
        (fun index bound => live (index + 1) (by omega))
      have trace := Execution.cons (transitions 0 (by omega)) later
      simpa only [live 0 (by omega), Nat.add_zero, max_self, Nat.add_comm] using trace

/-- The count comes from four actual loaded header words. No node or incidence
count is compiled into this fixed instruction block. -/
theorem header_count_execution (program : Program width 4) (s : State width 4)
    (base nodes children guards roots : ℕ)
    (pc : s.pc = word width base) (running : s.halted = false)
    (programFits : base + 16 < 2 ^ width)
    (countFits : 6 * nodes + children + guards + roots < 2 ^ width)
    (headerSize : 5 ≤ s.heap.size)
    (nodeWord : s.heap[1]'(by omega) = word width nodes)
    (childWord : s.heap[2]'(by omega) = word width children)
    (guardWord : s.heap[3]'(by omega) = word width guards)
    (rootWord : s.heap[4]'(by omega) = word width roots)
    (block : BlockAt program base (code width)) :
    Execution program s
      (scratchState s (base + 16) (word width (6 * nodes + children + guards + roots)) (word width roots))
      16 s.liveWords := by
  have v1 : (word width (1)).val = 1 := Nat.mod_eq_of_lt (by omega)
  have v2 : (word width (2)).val = 2 := Nat.mod_eq_of_lt (by omega)
  have v3 : (word width (3)).val = 3 := Nat.mod_eq_of_lt (by omega)
  have v4 : (word width (4)).val = 4 := Nat.mod_eq_of_lt (by omega)
  have vN : (word width (nodes)).val = nodes := Nat.mod_eq_of_lt (by omega)
  have v2N : (word width (2 * nodes)).val = 2 * nodes := Nat.mod_eq_of_lt (by omega)
  have v4N : (word width (4 * nodes)).val = 4 * nodes := Nat.mod_eq_of_lt (by omega)
  have v6N : (word width (6 * nodes)).val = 6 * nodes := Nat.mod_eq_of_lt (by omega)
  have vC : (word width (children)).val = children := Nat.mod_eq_of_lt (by omega)
  have vK : (word width (guards)).val = guards := Nat.mod_eq_of_lt (by omega)
  have vQ : (word width (roots)).val = roots := Nat.mod_eq_of_lt (by omega)
  have vNC : (word width (6 * nodes + children)).val = 6 * nodes + children := Nat.mod_eq_of_lt (by omega)
  have vNCK : (word width (6 * nodes + children + guards)).val = 6 * nodes + children + guards := Nat.mod_eq_of_lt (by omega)
  have vBase : (word width base).val = base := Nat.mod_eq_of_lt (by omega)
  have vNN : (word width (nodes + nodes)).val = nodes + nodes := Nat.mod_eq_of_lt (by omega)
  have vCN : (word width (children + 6 * nodes)).val = children + 6 * nodes :=
    Nat.mod_eq_of_lt (by omega)
  have vGCN : (word width (children + (guards + 6 * nodes))).val = children + (guards + 6 * nodes) :=
    Nat.mod_eq_of_lt (by omega)
  have addressFits (offset : ℕ) (bound : offset ≤ 16) : base + offset < 2 ^ width :=
    lt_of_le_of_lt (Nat.add_le_add_left bound base) programFits
  have p0 : (word width (base + 0)).val = base + 0 := Nat.mod_eq_of_lt (addressFits 0 (by decide))
  have p1 : (word width (base + 1)).val = base + 1 := Nat.mod_eq_of_lt (addressFits 1 (by decide))
  have p2 : (word width (base + 2)).val = base + 2 := Nat.mod_eq_of_lt (addressFits 2 (by decide))
  have p3 : (word width (base + 3)).val = base + 3 := Nat.mod_eq_of_lt (addressFits 3 (by decide))
  have p4 : (word width (base + 4)).val = base + 4 := Nat.mod_eq_of_lt (addressFits 4 (by decide))
  have p5 : (word width (base + 5)).val = base + 5 := Nat.mod_eq_of_lt (addressFits 5 (by decide))
  have p6 : (word width (base + 6)).val = base + 6 := Nat.mod_eq_of_lt (addressFits 6 (by decide))
  have p7 : (word width (base + 7)).val = base + 7 := Nat.mod_eq_of_lt (addressFits 7 (by decide))
  have p8 : (word width (base + 8)).val = base + 8 := Nat.mod_eq_of_lt (addressFits 8 (by decide))
  have p9 : (word width (base + 9)).val = base + 9 := Nat.mod_eq_of_lt (addressFits 9 (by decide))
  have p10 : (word width (base + 10)).val = base + 10 := Nat.mod_eq_of_lt (addressFits 10 (by decide))
  have p11 : (word width (base + 11)).val = base + 11 := Nat.mod_eq_of_lt (addressFits 11 (by decide))
  have p12 : (word width (base + 12)).val = base + 12 := Nat.mod_eq_of_lt (addressFits 12 (by decide))
  have p13 : (word width (base + 13)).val = base + 13 := Nat.mod_eq_of_lt (addressFits 13 (by decide))
  have p14 : (word width (base + 14)).val = base + 14 := Nat.mod_eq_of_lt (addressFits 14 (by decide))
  have p15 : (word width (base + 15)).val = base + 15 := Nat.mod_eq_of_lt (addressFits 15 (by decide))
  have p16 : (word width (base + 16)).val = base + 16 := Nat.mod_eq_of_lt (addressFits 16 (by decide))
  have transitions : ∀ index : Fin 16,
      programStep program (states s base nodes children guards roots index.val) =
        some (states s base nodes children guards roots (index.val + 1)) := by
    intro index
    have position : (states s base nodes children guards roots index.val).pc =
        word width (base + index.val) := by
      fin_cases index <;> rfl
    have instructionBound : index.val < (code width).length := by simpa only [code_length] using index.isLt
    have entry := block index.val instructionBound
    rw [fetched_block program _ (code width) base index.val position
      (addressFits index.val (Nat.le_of_lt index.isLt)) entry]
    fin_cases index
    all_goals simp [states, code, scratchState, step, State.advance, State.put, running, headerSize, nodeWord, childWord, guardWord, rootWord, v1, v2, v3, v4, vN, v2N, v4N, v6N, vC, vK, vQ, vNC, vNCK, vBase, vNN, vCN, vGCN, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, Nat.two_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    all_goals try constructor
    all_goals first
      | omega
      | rfl
      | (funext register; by_cases first : register = 0 <;>
          by_cases second : register = 1 <;> simp [first, second])
      | (congr 1 <;> omega)
    all_goals congr 1 <;> omega
  have trace := chain_execution program (states s base nodes children guards roots) 16 s.liveWords
    (fun index bound => transitions ⟨index, bound⟩)
    (by intro index bound; unfold states; split <;> rfl)
  simpa only [states, scratch_identity s base pc] using trace

/-- The header unrolling has the fixed literal size five, independent of all
source counts. The payload always uses the shared seven-instruction loop. -/
def fullCode (width base : ℕ) : Code width :=
  InputLoad.code (width := width) 5 ++ code width ++ ForestInputLoader.code width (base + 26)

@[simp] theorem fullCode_length (width base : ℕ) : (fullCode width base).length = 33 := by
  simp [fullCode]

/-- The resident program has constant size in the represented input counts. -/
theorem fullProgram_words (width base : ℕ) :
    programWords ((fullCode width base).toArray) = 132 := by
  simp [programWords]

private theorem allocate_header_transition (program : Program width 4) (heap : Array (Word width))
    (cursor : ℕ) (address loaded temporary : Word width) (fits : cursor < 2 ^ width)
    (room : heap.size < 2 ^ width) (entry : program[cursor]? = some (.allocate 0)) :
    programStep program (ForestCounter.counterState heap cursor address loaded temporary) =
      some (ForestCounter.counterState (heap.push address) (cursor + 1) address loaded temporary) := by
  unfold programStep
  rw [show (ForestCounter.counterState heap cursor address loaded temporary).pc.val = cursor from
    Nat.mod_eq_of_lt fits, entry]
  simp [step, ForestCounter.counterState, State.advance, room]
  rw [show (word width cursor).val = cursor from Nat.mod_eq_of_lt fits]

private theorem header_cell_execution (program : Program width 4) (heap : Array (Word width))
    (base : ℕ) (address loaded temporary value : Word width) (fits : base + 2 < 2 ^ width)
    (room : heap.size < 2 ^ width) (block : BlockAt program base InputLoad.cell) :
    Execution program ((ForestCounter.counterState heap base address loaded temporary).frame [value] [])
      (ForestCounter.counterState (heap.push value) (base + 2) value loaded temporary)
      2 (6 + heap.size) := by
  have first := ForestMarkerMachine.pop_transition program heap base address loaded temporary value
    (by omega) (by simpa [InputLoad.cell] using block 0 (by simp [InputLoad.cell]))
  have second := allocate_header_transition program heap (base + 1) value loaded temporary (by omega) room
    (by simpa [InputLoad.cell] using block 1 (by simp [InputLoad.cell]))
  have trace := Execution.cons first (Execution.cons second (Execution.refl
    (ForestCounter.counterState (heap.push value) (base + 2) value loaded temporary)))
  convert trace using 1 <;> simp only [ForestCounter.counterState_liveWords, State.frame_liveWords,
    List.length_cons, List.length_nil, Nat.add_zero, Array.size_push] <;> omega

/-- Register-preserving refinement used only at the fixed five-word header
prefix of fullCode. It does not supply a variable-sized payload program. -/
theorem header_values_execution (program : Program width 4) (heap : Array (Word width))
    (values : List (Word width)) (base : ℕ) (address loaded temporary : Word width)
    (fits : base + 2 * values.length < 2 ^ width)
    (room : heap.size + values.length ≤ 2 ^ width)
    (block : BlockAt program base (InputLoad.code values.length)) :
    ∃ finalAddress, Execution program
      ((ForestCounter.counterState heap base address loaded temporary).frame values [])
      (ForestCounter.counterState (heap ++ values.toArray) (base + 2 * values.length)
        finalAddress loaded temporary) (2 * values.length) (5 + heap.size + values.length) := by
  induction values generalizing heap base address with
  | nil =>
      refine ⟨address, ?_⟩
      have trace : Execution program (ForestCounter.counterState heap base address loaded temporary)
          (ForestCounter.counterState heap base address loaded temporary) 0 (5 + heap.size) := by
        simpa only [ForestCounter.counterState_liveWords] using
          Execution.refl (p := program) (ForestCounter.counterState heap base address loaded temporary)
      simpa [State.frame, ForestCounter.counterState] using trace
  | cons value rest ih =>
      have headBlock := BlockAt.prefix program base InputLoad.cell (InputLoad.code rest.length) block
      have first := (header_cell_execution program heap base address loaded temporary value
        (by simp only [List.length_cons] at fits; omega)
        (by simp only [List.length_cons] at room; omega) headBlock).frame rest []
      have tailBlock : BlockAt program (base + 2) (InputLoad.code rest.length) := by
        simpa [InputLoad.cell] using BlockAt.suffix program base InputLoad.cell (InputLoad.code rest.length) block
      obtain ⟨finalAddress, later⟩ := ih (heap.push value) (base + 2) value
        (by simp only [List.length_cons] at fits; omega)
        (by simp only [Array.size_push]; simp only [List.length_cons] at room; omega) tailBlock
      have joined := first.append later
      have finalHeap : heap.push value ++ rest.toArray = heap ++ (value :: rest).toArray := by
        apply Array.toList_inj.mp
        simp [List.append_assoc]
      refine ⟨finalAddress, ?_⟩
      have finalPosition : base + 2 + 2 * rest.length = base + 2 * (value :: rest).length := by
        simp only [List.length_cons]; omega
      rw [finalHeap, finalPosition] at joined
      convert joined using 1 <;>
        simp only [State.frame, ForestCounter.counterState, List.nil_append, List.append_nil,
          List.cons_append, List.length_nil, List.length_cons, Array.size_push, State.liveWords] <;> omega

def headerWords (width channels nodes children guards roots : ℕ) : List (Word width) :=
  [word width channels, word width nodes, word width children, word width guards, word width roots]

/-- A single graph-size-independent program loads the five source metadata
words, forms the remaining payload count from those words, and loads the exact
payload with its shared loop. Caller suffixes and output remain charged. -/
theorem cold_packet_execution (program : Program width 4)
    (base channels nodes children guards roots : ℕ) (payload suffix output : List (Word width))
    (address loaded temporary : Word width)
    (length_eq : payload.length = 6 * nodes + children + guards + roots)
    (fits : base + 33 < 2 ^ width) (room : 5 + payload.length ≤ 2 ^ width)
    (block : BlockAt program base (fullCode width base)) :
    ∃ final, Execution program
      ((ForestCounter.counterState (#[] : Array (Word width)) base address loaded temporary).frame
        (headerWords width channels nodes children guards roots ++ payload ++ suffix) output)
      final (27 + 7 * payload.length) (10 + payload.length + suffix.length + output.length) ∧
      final.heap = (headerWords width channels nodes children guards roots).toArray ++ payload.toArray ∧
      final.stack = suffix ∧ final.output = output ∧
      final.pc = word width (base + 33) ∧ final.halted = false := by
  let words := headerWords width channels nodes children guards roots
  let heap := words.toArray
  have wordsLength : words.length = 5 := rfl
  have heapSize : heap.size = 5 := by simp only [heap, List.size_toArray, wordsLength]
  have headerBlock : BlockAt program base (InputLoad.code (width := width) 5) :=
    BlockAt.prefix program base _ _ block
  have restBlock : BlockAt program (base + 10)
      (code width ++ ForestInputLoader.code width (base + 26)) := by
    simpa only [InputLoad.code_length, Nat.reduceMul, code, List.append_eq, List.cons_append, List.nil_append] using
      BlockAt.suffix program base (InputLoad.code (width := width) 5) _ block
  have metadataBlock : BlockAt program (base + 10) (code width) :=
    BlockAt.prefix program (base + 10) _ _ restBlock
  have payloadBlock : BlockAt program (base + 26) (ForestInputLoader.code width (base + 26)) := by
    simpa only [code_length, Nat.add_assoc, Nat.reduceAdd] using
      BlockAt.suffix program (base + 10) (code width) _ restBlock
  obtain ⟨headerAddress, headerTrace⟩ := header_values_execution program (#[] : Array (Word width))
    words base address loaded temporary (by rw [wordsLength]; omega)
    (by simp only [Array.size_empty, wordsLength]; omega) (by simpa only [wordsLength] using headerBlock)
  have headerLoaded := headerTrace.frame (payload ++ suffix) output
  let ready := ForestCounter.counterState heap (base + 10) headerAddress loaded temporary
  have countFits : 6 * nodes + children + guards + roots < 2 ^ width := by rw [← length_eq]; omega
  have counted := header_count_execution program ready (base + 10) nodes children guards roots rfl rfl
    (by omega) countFits (by simpa only [ready, ForestCounter.counterState, heapSize] using (le_refl 5))
    (by simp [ready, ForestCounter.counterState, heap, words, headerWords])
    (by simp [ready, ForestCounter.counterState, heap, words, headerWords])
    (by simp [ready, ForestCounter.counterState, heap, words, headerWords])
    (by simp [ready, ForestCounter.counterState, heap, words, headerWords]) metadataBlock
  have countedState : scratchState ready (base + 10 + 16)
      (word width (6 * nodes + children + guards + roots)) (word width roots) =
      ForestCounter.counterState heap (base + 26) (word width payload.length) (word width roots) temporary := by
    rw [← length_eq]
    have position : base + 10 + 16 = base + 26 := by omega
    rw [position]
    unfold scratchState ready ForestCounter.counterState
    congr 1
    funext register
    by_cases first : register = 0
    · subst register; simp
    · by_cases second : register = 1 <;> simp [first, second]
  rw [countedState] at counted
  have readyLive : ready.liveWords = 10 := by
    simp only [ready, ForestCounter.counterState_liveWords, heapSize]
  rw [readyLive] at counted
  have countLoaded := counted.frame (payload ++ suffix) output
  obtain ⟨afterPayload, payloadTrace, finalHeap, finalStack, finalOutput, finalPC, active⟩ :=
    ForestInputLoader.load_words_execution program heap payload (base + 26) (word width roots) temporary
      (by omega) (by rw [length_eq]; exact countFits) (by rw [heapSize]; exact room) payloadBlock
  have payloadLoaded := payloadTrace.frame suffix output
  have joined := (headerLoaded.append countLoaded).append payloadLoaded
  refine ⟨afterPayload.frame suffix output, ?_, ?_, ?_, ?_, ?_, active⟩
  · convert joined using 1 <;>
      simp only [ready, heap, wordsLength, heapSize, Array.empty_append, Array.size_empty,
        ForestCounter.counterState_liveWords, State.frame, List.nil_append, List.append_nil,
        List.length_append, List.length_nil, List.append_assoc, State.liveWords]
    all_goals first | omega | (congr 1 <;> omega)
  · simpa only [State.frame, heap, words] using finalHeap
  · simp only [State.frame, finalStack, List.nil_append]
  · simp only [State.frame, finalOutput, List.nil_append]
  · simpa only [State.frame, Nat.add_assoc, Nat.reduceAdd] using finalPC

end Controller.Cost.ForestInputMetadata
