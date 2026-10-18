module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Refinement
public import Lean.Elab.Tactic.Omega
public import Mathlib.Data.List.Induction

@[expose] public section

/-! Fixed instruction blocks for transferring packets whose addresses and sizes
are supplied by executed runtime metadata. Program storage is independent of
packet length and of the retained normalized dependency incidence count. -/
namespace Controller.Cost.RawTransferLoops

def countedReleaseCode (width entry done : Nat) : Program width 8 :=
  #[.branchZero 0 (word width done), .release, .add 0 0 7,
    .branchZero 6 (word width entry)]

def reverseSaveCode (width entry done : Nat) : Program width 8 :=
  #[.branchZero 0 (word width done), .load 5 1, .push 5,
    .add 1 1 7, .add 0 0 7, .branchZero 6 (word width entry)]

def CodeAt (resident : Program width 8) (entry : Nat) (code : Program width 8) : Prop :=
  ∀ phase : Fin code.size, resident[entry + phase.val]? = code[phase.val]?

@[simp] theorem countedReleaseCode_size (width entry done : Nat) :
    (countedReleaseCode width entry done).size = 4 := rfl

@[simp] theorem reverseSaveCode_size (width entry done : Nat) :
    (reverseSaveCode width entry done).size = 6 := rfl

theorem fetched (resident : Program width 8) (state : State width 8)
    (address : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width address) (fits : address < 2 ^ width)
    (present : resident[address]? = some instruction) :
    programStep resident state = step instruction state := by
  have value : state.pc.val = address := by
    rw [position]
    exact Nat.mod_eq_of_lt fits
  simp only [programStep, value, present, Option.bind_some]
  rfl

theorem advance_position (state : State width 8) (position : state.pc = word width address)
    (fits : address < 2 ^ width) : state.advance.pc = word width (address + 1) := by
  have value : state.pc.val = address := by
    rw [position]
    exact Nat.mod_eq_of_lt fits
  simp only [State.advance, value]

theorem decrement_word (width value : Nat) :
    word width (value + 1 + (2 ^ width - 1)) = word width value := by
  have positive := Nat.two_pow_pos width
  have arithmetic : value + 1 + (2 ^ width - 1) = value + 2 ^ width := by omega
  apply Fin.ext
  simp only [word, arithmetic, Nat.add_mod_right]

/-- The release loop reads its count from register zero. -/
theorem release_zero_step (resident : Program width 8) (entry done : Nat)
    (state : State width 8) (position : state.pc = word width entry)
    (fits : entry < 2 ^ width) (running : state.halted = false)
    (zero : (state.reg 0).val = 0)
    (atCode : CodeAt resident entry (countedReleaseCode width entry done)) :
    programStep resident state = some { state.advance with pc := word width done } := by
  have present : resident[entry]? = some (.branchZero 0 (word width done)) := by
    simpa [countedReleaseCode] using atCode ⟨0, by simp⟩
  rw [fetched resident state entry _ position fits present]
  simp [step, running, zero]

/-- The save loop also tests a runtime count before any memory access. -/
theorem save_zero_step (resident : Program width 8) (entry done : Nat)
    (state : State width 8) (position : state.pc = word width entry)
    (fits : entry < 2 ^ width) (running : state.halted = false)
    (zero : (state.reg 0).val = 0)
    (atCode : CodeAt resident entry (reverseSaveCode width entry done)) :
    programStep resident state = some { state.advance with pc := word width done } := by
  have present : resident[entry]? = some (.branchZero 0 (word width done)) := by
    simpa [reverseSaveCode] using atCode ⟨0, by simp⟩
  rw [fetched resident state entry _ position fits present]
  simp [step, running, zero]

private theorem release_round (resident : Program width 8) (entry done count : Nat)
    (state : State width 8) (position : state.pc = word width entry)
    (room : entry + 4 < 2 ^ width) (running : state.halted = false)
    (heapCount : state.heap.size = count + 1) (countFits : count + 1 < 2 ^ width)
    (countReg : state.reg 0 = word width (count + 1))
    (maskReg : state.reg 7 = word width (2 ^ width - 1)) (zeroReg : state.reg 6 = word width 0)
    (atCode : CodeAt resident entry (countedReleaseCode width entry done)) :
    ∃ next peak, Execution resident state next 4 peak ∧ peak ≤ state.liveWords ∧
      next.pc = word width entry ∧ next.halted = false ∧ next.heap = state.heap.pop ∧
      next.heap.size = count ∧ next.stack = state.stack ∧ next.output = state.output ∧
      next.reg 0 = word width count ∧
      (∀ index : Fin 8, index ≠ 0 → next.reg index = state.reg index) := by
  let s1 := state.advance
  let s2 := { s1.advance with heap := state.heap.pop }
  let s3 := s2.advance.put 0 (word width count)
  let next := { s3.advance with pc := word width entry }
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pc1 : s1.pc = word width (entry + 1) := advance_position state position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    exact advance_position s1 pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    exact advance_position s2 pc2 (by omega)
  have code0 : resident[entry]? = some (.branchZero 0 (word width done)) := by
    simpa [countedReleaseCode] using atCode ⟨0, by simp⟩
  have code1 : resident[entry + 1]? = some .release := by
    simpa [countedReleaseCode] using atCode ⟨1, by simp⟩
  have code2 : resident[entry + 2]? = some (.add 0 0 7) := by
    simpa [countedReleaseCode] using atCode ⟨2, by simp⟩
  have code3 : resident[entry + 3]? = some (.branchZero 6 (word width entry)) := by
    simpa [countedReleaseCode] using atCode ⟨3, by simp⟩
  have countValue : (state.reg 0).val = count + 1 := by
    rw [countReg]; exact Nat.mod_eq_of_lt countFits
  have maskValue : (state.reg 7).val = 2 ^ width - 1 := by
    rw [maskReg]; exact Nat.mod_eq_of_lt maskFits
  have active : state.heap.isEmpty = false := Array.isEmpty_eq_false_iff.mpr (by
    intro empty; rw [empty] at heapCount; simp at heapCount)
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state entry _ position (by omega) code0]
    simp [step, running, countValue, s1]
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) _ pc1 (by omega) code1]
    simp [step, s1, State.advance, running, active, s2]
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) _ pc2 (by omega) code2]
    have v0 : (s2.reg 0).val = count + 1 := countValue
    have v7 : (s2.reg 7).val = 2 ^ width - 1 := maskValue
    simp only [step, show s2.halted = false from running, Bool.false_eq_true, ite_false, v0, v7]
    rw [decrement_word]
  have t3 : programStep resident s3 = some next := by
    rw [fetched resident s3 (entry + 3) _ pc3 (by omega) code3]
    simp [step, s3, s2, s1, State.advance, State.put, running, zeroReg, word, next]
  have l1 : s1.liveWords = state.liveWords := rfl
  have l2 : s2.liveWords ≤ state.liveWords := by
    simp only [s2, s1, State.liveWords, State.advance, Array.size_pop]; omega
  have l3 : s3.liveWords = s2.liveWords := rfl
  have ln : next.liveWords = s2.liveWords := rfl
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.refl next))))
  have peakEqual : max state.liveWords (max s1.liveWords
      (max s2.liveWords (max s3.liveWords next.liveWords))) = state.liveWords := by omega
  refine ⟨next, state.liveWords, ?_, le_rfl, rfl, running, rfl, ?_, rfl, rfl, ?_, ?_⟩
  · simpa only [Nat.zero_add, peakEqual] using trace
  · simp only [next, s3, s2, State.advance, State.put, Array.size_pop, heapCount]; omega
  · simp [next, s3, State.advance, State.put]
  · intro index different
    simp [next, s3, s2, s1, State.advance, State.put, different]

/-- Release every heap word using a runtime count; program storage stays fixed.
No implicit memory fault is used as a termination test. -/
theorem counted_release_execution (resident : Program width 8) (entry done : Nat)
    (count : Nat) :
    ∀ state : State width 8, state.pc = word width entry → state.halted = false →
      entry + 4 < 2 ^ width → state.heap.size = count → count < 2 ^ width →
      state.reg 0 = word width count → state.reg 7 = word width (2 ^ width - 1) →
      state.reg 6 = word width 0 → CodeAt resident entry (countedReleaseCode width entry done) →
    ∃ final peak, Execution resident state final (4 * count + 1) peak ∧ peak ≤ state.liveWords ∧
      final.heap = #[] ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 0 = word width 0 ∧
      (∀ index : Fin 8, index ≠ 0 → final.reg index = state.reg index) := by
  induction count with
  | zero =>
    intro state position running room heapCount countFits countReg maskReg zeroReg atCode
    let final := { state.advance with pc := word width done }
    have transition : programStep resident state = some final :=
      release_zero_step resident entry done state position (by omega) running
        (by rw [countReg]; simp [word]) atCode
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, state.liveWords, ?_, le_rfl, Array.eq_empty_of_size_eq_zero heapCount,
      rfl, rfl, rfl, running, countReg, ?_⟩
    · simpa only [live, Nat.max_self] using Execution.cons transition (Execution.refl final)
    · intro index different; rfl
  | succ count ih =>
    intro state position running room heapCount countFits countReg maskReg zeroReg atCode
    obtain ⟨middle, firstPeak, first, firstBound, middlePC, middleRunning, middleHeap,
      middleCount, middleStack, middleOutput, middleReg, middleFrame⟩ :=
      release_round resident entry done count state position room running heapCount countFits
        countReg maskReg zeroReg atCode
    have middleLive : middle.liveWords ≤ state.liveWords :=
      (Execution.final_storage_le first).trans firstBound
    obtain ⟨final, lastPeak, last, lastBound, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalReg, finalFrame⟩ :=
      ih middle middlePC middleRunning room middleCount (by omega) middleReg
        ((middleFrame 7 (by decide)).trans maskReg) ((middleFrame 6 (by decide)).trans zeroReg) atCode
    refine ⟨final, max firstPeak lastPeak, ?_, Nat.max_le.mpr
      ⟨firstBound, lastBound.trans middleLive⟩, finalHeap, finalStack.trans middleStack,
      finalOutput.trans middleOutput, finalPC, finalRunning, finalReg, ?_⟩
    · have total : 4 + (4 * count + 1) = 4 * (count + 1) + 1 := by omega
      simpa only [total] using first.append last
    · intro index different
      exact (finalFrame index different).trans (middleFrame index different)

private theorem decrement_positive (width address : Nat) (positive : 0 < address) :
    word width (address + (2 ^ width - 1)) = word width (address - 1) := by
  have same : address = address - 1 + 1 := by omega
  conv_lhs => rw [same]
  exact decrement_word width (address - 1)

private theorem save_round (resident : Program width 8) (entry done count address : Nat)
    (value : Word width) (state : State width 8) (position : state.pc = word width entry)
    (room : entry + 6 < 2 ^ width) (running : state.halted = false)
    (countFits : count + 1 < 2 ^ width) (addressFits : address < 2 ^ width)
    (positive : 0 < address) (cell : state.heap[address]? = some value)
    (countReg : state.reg 0 = word width (count + 1))
    (cursorReg : state.reg 1 = word width address)
    (maskReg : state.reg 7 = word width (2 ^ width - 1)) (zeroReg : state.reg 6 = word width 0)
    (atCode : CodeAt resident entry (reverseSaveCode width entry done)) :
    ∃ next peak, Execution resident state next 6 peak ∧ peak ≤ state.liveWords + 1 ∧
      next.liveWords = state.liveWords + 1 ∧ next.pc = word width entry ∧ next.halted = false ∧
      next.heap = state.heap ∧ next.stack = value :: state.stack ∧ next.output = state.output ∧
      next.reg 0 = word width count ∧ next.reg 1 = word width (address - 1) ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 1 → index ≠ 5 → next.reg index = state.reg index) := by
  let s1 := state.advance
  let s2 := s1.advance.put 5 value
  let s3 := { s2.advance with stack := value :: state.stack }
  let s4 := s3.advance.put 1 (word width (address - 1))
  let s5 := s4.advance.put 0 (word width count)
  let next := { s5.advance with pc := word width entry }
  have maskFits : 2 ^ width - 1 < 2 ^ width := by have := Nat.two_pow_pos width; omega
  have pc1 : s1.pc = word width (entry + 1) := advance_position state position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := advance_position s1 pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := advance_position s2 pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := advance_position s3 pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := advance_position s4 pc4 (by omega)
  have code0 : resident[entry]? = some (.branchZero 0 (word width done)) := by
    simpa [reverseSaveCode] using atCode ⟨0, by simp⟩
  have code1 : resident[entry + 1]? = some (.load 5 1) := by
    simpa [reverseSaveCode] using atCode ⟨1, by simp⟩
  have code2 : resident[entry + 2]? = some (.push 5) := by
    simpa [reverseSaveCode] using atCode ⟨2, by simp⟩
  have code3 : resident[entry + 3]? = some (.add 1 1 7) := by
    simpa [reverseSaveCode] using atCode ⟨3, by simp⟩
  have code4 : resident[entry + 4]? = some (.add 0 0 7) := by
    simpa [reverseSaveCode] using atCode ⟨4, by simp⟩
  have code5 : resident[entry + 5]? = some (.branchZero 6 (word width entry)) := by
    simpa [reverseSaveCode] using atCode ⟨5, by simp⟩
  have countValue : (state.reg 0).val = count + 1 := by
    rw [countReg]; exact Nat.mod_eq_of_lt countFits
  have cursorValue : (state.reg 1).val = address := by
    rw [cursorReg]; exact Nat.mod_eq_of_lt addressFits
  have maskValue : (state.reg 7).val = 2 ^ width - 1 := by
    rw [maskReg]; exact Nat.mod_eq_of_lt maskFits
  have inside : address < state.heap.size := Array.getElem?_eq_some_iff.mp cell |>.1
  have actual : state.heap[address] = value := by
    rw [Array.getElem?_eq_getElem inside] at cell
    exact Option.some.inj cell
  have t0 : programStep resident state = some s1 := by
    rw [fetched resident state entry _ position (by omega) code0]
    simp [step, running, countValue, s1]
  have t1 : programStep resident s1 = some s2 := by
    rw [fetched resident s1 (entry + 1) _ pc1 (by omega) code1]
    simp [step, s1, State.advance, running, cursorValue, inside, actual, s2]
  have t2 : programStep resident s2 = some s3 := by
    rw [fetched resident s2 (entry + 2) _ pc2 (by omega) code2]
    simp [step, s2, s1, State.advance, State.put, running, s3]
  have t3 : programStep resident s3 = some s4 := by
    rw [fetched resident s3 (entry + 3) _ pc3 (by omega) code3]
    have v1 : (s3.reg 1).val = address := by simp [s3, s2, s1, State.advance, State.put, cursorValue]
    have v7 : (s3.reg 7).val = 2 ^ width - 1 := by simp [s3, s2, s1, State.advance, State.put, maskValue]
    simp only [step, show s3.halted = false from running, Bool.false_eq_true, ite_false, v1, v7]
    rw [decrement_positive width address positive]
  have t4 : programStep resident s4 = some s5 := by
    rw [fetched resident s4 (entry + 4) _ pc4 (by omega) code4]
    have v0 : (s4.reg 0).val = count + 1 := by simp [s4, s3, s2, s1, State.advance, State.put, countValue]
    have v7 : (s4.reg 7).val = 2 ^ width - 1 := by simp [s4, s3, s2, s1, State.advance, State.put, maskValue]
    simp only [step, show s4.halted = false from running, Bool.false_eq_true, ite_false, v0, v7]
    rw [decrement_word]
  have t5 : programStep resident s5 = some next := by
    rw [fetched resident s5 (entry + 5) _ pc5 (by omega) code5]
    simp [step, s5, s4, s3, s2, s1, State.advance, State.put, running, zeroReg, word, next]
  have l1 : s1.liveWords = state.liveWords := rfl
  have l2 : s2.liveWords = state.liveWords := rfl
  have l3 : s3.liveWords = state.liveWords + 1 := by simp [s3, s2, s1, State.liveWords, State.advance, State.put]; omega
  have l4 : s4.liveWords = state.liveWords + 1 := l3
  have l5 : s5.liveWords = state.liveWords + 1 := l3
  have ln : next.liveWords = state.liveWords + 1 := l3
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2
    (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl next))))))
  have peakEqual : max state.liveWords (max s1.liveWords (max s2.liveWords
      (max s3.liveWords (max s4.liveWords (max s5.liveWords next.liveWords))))) = state.liveWords + 1 := by omega
  refine ⟨next, state.liveWords + 1, ?_, le_rfl, ln, rfl, running, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add, peakEqual] using trace
  · simp [next, s5, State.advance, State.put]
  · simp [next, s5, s4, State.advance, State.put]
  · intro index n0 n1 n5
    simp [next, s5, s4, s3, s2, s1, State.advance, State.put, n0, n1, n5]

/-- Every packet word is fetched once and pushed in reverse traversal order,
so the final stack contains the packet in its original order. -/
theorem reverse_save_execution (resident : Program width 8) (entry done base : Nat)
    (packet : List (Word width)) :
    ∀ state : State width 8, state.pc = word width entry → state.halted = false →
      entry + 6 < 2 ^ width → 0 < base → base + packet.length < 2 ^ width →
      packet.length < 2 ^ width → state.reg 0 = word width packet.length →
      state.reg 1 = word width (base + packet.length - 1) →
      state.reg 7 = word width (2 ^ width - 1) → state.reg 6 = word width 0 →
      (∀ index : Nat, ∀ h : index < packet.length,
        state.heap[base + index]? = some packet[index]) →
      CodeAt resident entry (reverseSaveCode width entry done) →
    ∃ final peak, Execution resident state final (6 * packet.length + 1) peak ∧
      peak ≤ state.liveWords + packet.length ∧ final.heap = state.heap ∧
      final.stack = packet ++ state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧ final.reg 0 = word width 0 ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 1 → index ≠ 5 → final.reg index = state.reg index) := by
  induction packet using List.reverseRecOn with
  | nil =>
    intro state position running room positive packetFits countFits countReg cursorReg maskReg zeroReg cells atCode
    let final := { state.advance with pc := word width done }
    have transition : programStep resident state = some final :=
      save_zero_step resident entry done state position (by omega) running
        (by rw [countReg]; simp [word]) atCode
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, state.liveWords, ?_, by simp, rfl, by simp [final, State.advance], rfl,
      rfl, running, countReg, ?_⟩
    · simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, live, Nat.max_self]
        using Execution.cons transition (Execution.refl final)
    · intro index n0 n1 n5; rfl
  | append_singleton packet value ih =>
    intro state position running room positive packetFits countFits countReg cursorReg maskReg zeroReg cells atCode
    have lastCell : state.heap[base + packet.length]? = some value := by
      simpa using cells packet.length (by simp)
    have countReg' : state.reg 0 = word width (packet.length + 1) := by simpa using countReg
    have cursorReg' : state.reg 1 = word width (base + packet.length) := by
      convert cursorReg using 1 <;> simp <;> omega
    obtain ⟨middle, firstPeak, first, firstBound, middleLive, middlePC, middleRunning,
      middleHeap, middleStack, middleOutput, middleCount, middleCursor, middleFrame⟩ :=
      save_round resident entry done packet.length (base + packet.length) value state position room running
        (by simpa using countFits) (by simp at packetFits; omega) (by omega) lastCell
        countReg' cursorReg' maskReg zeroReg atCode
    have prefixCells : ∀ index : Nat, ∀ h : index < packet.length,
        middle.heap[base + index]? = some packet[index] := by
      intro index h
      rw [middleHeap]
      have original := cells index (by simp; omega)
      exact original.trans (congrArg some (List.getElem_append_left' h [value]).symm)
    obtain ⟨final, lastPeak, last, lastBound, finalHeap, finalStack, finalOutput,
      finalPC, finalRunning, finalReg, finalFrame⟩ :=
      ih middle middlePC middleRunning room positive (by simp at packetFits; omega)
        (by simp at countFits; omega) middleCount middleCursor
        ((middleFrame 7 (by decide) (by decide) (by decide)).trans maskReg)
        ((middleFrame 6 (by decide) (by decide) (by decide)).trans zeroReg) prefixCells atCode
    refine ⟨final, max firstPeak lastPeak, ?_, ?_, finalHeap.trans middleHeap, ?_,
      finalOutput.trans middleOutput, finalPC, finalRunning, finalReg, ?_⟩
    · have total : 6 + (6 * packet.length + 1) = 6 * (packet ++ [value]).length + 1 := by simp; omega
      simpa only [total] using first.append last
    · simp only [List.length_append, List.length_singleton]
      rw [middleLive] at lastBound
      exact Nat.max_le.mpr ⟨by omega, by omega⟩
    · rw [finalStack, middleStack]
      simp [List.append_assoc]
    · intro index n0 n1 n5
      exact (finalFrame index n0 n1 n5).trans (middleFrame index n0 n1 n5)

end Controller.Cost.RawTransferLoops
