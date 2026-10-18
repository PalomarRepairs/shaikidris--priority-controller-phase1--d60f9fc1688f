module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationSteps
public import Controller.Cost.SharedDetectorAssembly

@[expose] public section

/-! Reads for a selected expansion use the stored selector bit and the two
original child cells. A shared AND is read once for its selected occurrence. -/
namespace Controller.Extensions.ResolvedSourceRead
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

def readCode (width address : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width address), .load 1 0]

@[simp] theorem readCode_length : (readCode width address).length = 2 := rfl

theorem read_execution (program : Program width 8) (state : State width 8)
    (entry address : Nat) (value : Word width)
    (stored : state.heap[address]? = some value)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 2 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (readCode width address)) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.reg 1 = value ∧ final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry + 2) ∧ final.halted = false ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 1 → final.reg i = state.reg i) := by
  have bound := (Array.getElem?_eq_some_iff.mp stored).1
  have cell := (Array.getElem?_eq_some_iff.mp stored).2
  have addressVal : (word width address).val = address := Nat.mod_eq_of_lt (by omega)
  obtain ⟨middle, first, pc, reg, heap, stack, output, active, frame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry address 0 state position running (by omega)
      (by simpa [readCode] using present 0 (by simp))
  obtain ⟨final, last, fp, fr, fh, fs, fo, fa, ff⟩ :=
    EnumerationSteps.load_execution program middle (entry+1) 1 0 pc active (by omega)
      (by simpa only [reg, addressVal, heap] using bound)
      (by simpa [readCode] using present 1 (by simp))
  have live : middle.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  refine ⟨final, by simpa only [live, Nat.max_self] using first.append last,
    ?_, fh.trans heap, fs.trans stack, fo.trans output, ?_, fa, ?_⟩
  · calc
      final.reg 1 = state.heap[address] := by simpa only [reg, addressVal, heap] using fr
      _ = value := cell
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using fp
  · intro i h0 h1; rw [ff i h1, frame i h0]

def choiceCode (width entry flag left right : Nat) : List (Instruction width 8) :=
  readCode width flag ++
    ([.branchZero 1 (word width (entry + 7))] ++
    (readCode width right ++
    ([.constant 0 (word width 0), .branchZero 0 (word width (entry + 9))] ++ readCode width left)))

@[simp] theorem choiceCode_length : (choiceCode width entry flag left right).length = 9 := by
  simp [choiceCode]

theorem choice_execution (program : Program width 8) (state : State width 8)
    (entry flag left right : Nat) (selected : Bool) (firstValue secondValue : Word width)
    (flagStored : state.heap[flag]? = some (boolWord width selected))
    (leftStored : state.heap[left]? = some firstValue) (rightStored : state.heap[right]? = some secondValue)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 9 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (choiceCode width entry flag left right)) :
    ∃ final ticks, Execution program state final ticks state.liveWords ∧ ticks ≤ 7 ∧
      final.reg 1 = (if selected then secondValue else firstValue) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry + 9) ∧ final.halted = false ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 1 → final.reg i = state.reg i) := by
  unfold choiceCode at present
  have flagAt := block_left program entry _ _ present
  have afterFlag := block_right program entry _ _ present
  simp only [readCode_length] at afterFlag
  have branchAt : program[entry+2]? = some (.branchZero 1 (word width (entry+7))) := by
    simpa using afterFlag 0 (by simp)
  have afterBranch := block_right program (entry+2) _ _ afterFlag
  simp only [List.length_singleton] at afterBranch
  have rightAt := block_left program (entry+3) _ _ afterBranch
  have afterRight := block_right program (entry+3) _ _ afterBranch
  simp only [readCode_length] at afterRight
  have jumpAt := block_left program (entry+5) _ _ afterRight
  have leftAt := block_right program (entry+5) _ _ afterRight
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at leftAt
  obtain ⟨tested, t1, v1, h1, s1, o1, p1, r1, f1⟩ :=
    read_execution program state entry flag _ flagStored position running (by omega) heapFits flagAt
  have live1 : tested.liveWords = state.liveWords := by simp only [State.liveWords, h1, s1, o1]
  cases selected with
  | false =>
    obtain ⟨branched, t2, p2, h2, s2, o2, r2, f2⟩ :=
      EnumerationSteps.branch_taken program tested (entry+2) (entry+7) 1 p1 r1 (by omega)
        (by rw [v1]; simp [boolWord, word]) branchAt
    obtain ⟨final, t3, v3, h3, s3, o3, p3, r3, f3⟩ :=
      read_execution program branched (entry+7) left firstValue (by simpa [h2, h1] using leftStored)
        p2 r2 (by omega) (by simpa [h2, h1] using heapFits)
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using leftAt)
    have live2 : branched.liveWords = state.liveWords := by simp only [State.liveWords, h2, s2, o2, h1, s1, o1]
    refine ⟨final, 5, by simpa only [live1, live2, Nat.max_self] using t1.append (t2.append t3),
      by decide, v3, h3.trans (h2.trans h1), s3.trans (s2.trans s1), o3.trans (o2.trans o1), ?_, r3, ?_⟩
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using p3
    · intro i h0 h1; rw [f3 i h0 h1, f2, f1 i h0 h1]
  | true =>
    obtain ⟨branched, t2, p2, h2, s2, o2, r2, f2⟩ :=
      EnumerationSteps.branch_skipped program tested (entry+2) (entry+7) 1 p1 r1 (by omega)
        (by rw [v1]; simp [boolWord, word, Nat.mod_eq_of_lt (by omega : 1 < 2^width)]) branchAt
    obtain ⟨loaded, t3, v3, h3, s3, o3, p3, r3, f3⟩ :=
      read_execution program branched (entry+3) right secondValue (by simpa [h2, h1] using rightStored)
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using p2) r2 (by omega)
        (by simpa [h2, h1] using heapFits)
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using rightAt)
    obtain ⟨final, t4, p4, h4, s4, o4, r4, f4⟩ :=
      EnumerationSteps.jump_execution program loaded (entry+5) (entry+9)
        (by simpa only [Nat.add_assoc, Nat.reduceAdd] using p3) r3 (by omega)
        (by simpa using jumpAt 0 (by simp)) (by simpa using jumpAt 1 (by simp))
    have live2 : branched.liveWords = state.liveWords := by simp only [State.liveWords, h2, s2, o2, h1, s1, o1]
    have live3 : loaded.liveWords = state.liveWords := by simp only [State.liveWords, h3, s3, o3, h2, s2, o2, h1, s1, o1]
    refine ⟨final, 7, by simpa only [live1, live2, live3, Nat.max_self] using t1.append (t2.append (t3.append t4)),
      le_rfl, (f4 1 (by decide)).trans v3, h4.trans (h3.trans (h2.trans h1)),
      s4.trans (s3.trans (s2.trans s1)), o4.trans (o3.trans (o2.trans o1)), p4, r4, ?_⟩
    intro i h0 h1; rw [f4 i h0, f3 i h0 h1, f2, f1 i h0 h1]

def pushCode (width address : Nat) : List (Instruction width 8) := readCode width address ++ [.push 1]

@[simp] theorem pushCode_length : (pushCode width address).length = 3 := by simp [pushCode]

theorem push_execution (program : Program width 8) (state : State width 8)
    (entry address : Nat) (value : Word width) (stored : state.heap[address]? = some value)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry+3 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (pushCode width address)) :
    ∃ final, Execution program state final 3 (state.liveWords+1) ∧
      final.heap = state.heap ∧ final.stack = value :: state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry+3) ∧ final.halted = false ∧ final.reg 4 = state.reg 4 := by
  have readAt := block_left program entry _ _ present
  have pushAt := block_right program entry _ _ present
  simp only [readCode_length] at pushAt
  obtain ⟨middle, first, reg, heap, stack, output, pc, active, frame⟩ :=
    read_execution program state entry address value stored position running (by omega) heapFits readAt
  obtain ⟨final, last, fp, fh, fs, fo, fr, ff, _⟩ :=
    EnumerationSteps.push_execution program middle (entry+2) 1 pc active (by omega)
      (by simpa using pushAt 0 (by simp))
  have live : middle.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  refine ⟨final, by simpa only [live, Nat.max_eq_right (Nat.le_succ _)] using first.append last,
    fh.trans heap, by rw [fs, reg, stack], fo.trans output, ?_, fr, (ff 4).trans (frame 4 (by decide) (by decide))⟩
  simpa only [Nat.add_assoc, Nat.reduceAdd] using fp

end Controller.Extensions.ResolvedSourceRead
