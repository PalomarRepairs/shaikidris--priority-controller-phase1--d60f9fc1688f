module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.ForestZeroAnswer

@[expose] public section

/-! A fetched countdown loop releases query-local suffix words. The caller
supplies the physical count and retained boundary; the loop preserves every
cell below that boundary and emits no additional output. -/
set_option autoImplicit false
namespace Controller.Cost.ForestZeroReclaim
open Controller.Cost Controller.Cost.ForestZeroBackendFrame
variable {width : Nat}

def code (width entry returnPc : Nat) : Program width 8 :=
  #[.branchZero 0 (word width returnPc), .release,
    .add 0 0 6, .branchZero 2 (word width entry)]

def At (program : Program width 8) (entry returnPc : Nat) : Prop :=
  ∀ phase : Fin 4, program[entry + phase.val]? = (code width entry returnPc)[phase.val]?

private theorem fetched (program : Program width 8) (state : State width 8)
    (entry : Nat) (instruction : Instruction width 8)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width)
    (present : program[entry]? = some instruction) :
    programStep program state = step instruction state := by
  unfold programStep
  rw [position, show (word width entry).val = entry from Nat.mod_eq_of_lt fits, present]
  rfl

private theorem next_pc (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (fits : entry < 2 ^ width) :
    state.advance.pc = word width (entry + 1) := by
  simp only [State.advance, position, show (word width entry).val = entry from Nat.mod_eq_of_lt fits]

private theorem decrement (count : Nat) (fits : count + 1 < 2 ^ width) :
    word width ((word width (count + 1)).val + (word width (2 ^ width - 1)).val) =
      word width count := by
  have positive : 0 < 2 ^ width := Nat.two_pow_pos width
  have minusFits : 2 ^ width - 1 < 2 ^ width := by omega
  rw [show (word width (count + 1)).val = count + 1 from Nat.mod_eq_of_lt fits,
    show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from Nat.mod_eq_of_lt minusFits]
  have sum : count + 1 + (2 ^ width - 1) = count + 2 ^ width := by omega
  simp only [sum, word, Nat.add_mod_right]

theorem execution (program : Program width 8) (entry returnPc keep count : Nat)
    (state : State width 8) (present : At program entry returnPc)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 4 < 2 ^ width) (countFits : count < 2 ^ width)
    (countStored : state.reg 0 = word width count)
    (minusStored : state.reg 6 = word width (2 ^ width - 1))
    (zeroStored : state.reg 2 = word width 0)
    (size : state.heap.size = keep + count) :
    ∃ final, Execution program state final (4 * count + 1) state.liveWords ∧
      final.heap.size = keep ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap := by
  induction count generalizing state with
  | zero =>
    let final : State width 8 := { state.advance with pc := word width returnPc }
    have transition : programStep program state = some final := by
      rw [fetched program state entry (.branchZero 0 (word width returnPc)) position
        (by omega) (by simpa [At, code] using present ⟨0, by decide⟩)]
      simp [step, running, countStored, word, final]
    have live : final.liveWords = state.liveWords := rfl
    refine ⟨final, ?_, by simpa [final, State.advance] using size, rfl, rfl, rfl, running, ?_⟩
    · simpa only [live, Nat.max_self, Nat.reduceAdd, Nat.mul_zero] using
        Execution.cons transition (Execution.refl final)
    · exact ForestZeroBackendFrame.refl state.heap (by omega)
  | succ count ih =>
    let s1 := state.advance
    let s2 : State width 8 := { s1.advance with heap := state.heap.pop }
    let s3 := s2.advance.put 0 (word width count)
    let s4 : State width 8 := { s3.advance with pc := word width entry }
    have pc1 : s1.pc = word width (entry + 1) := next_pc state entry position (by omega)
    have pc2 : s2.pc = word width (entry + 2) := by
      simpa [s2, Nat.add_assoc] using next_pc s1 (entry + 1) pc1 (by omega)
    have pc3 : s3.pc = word width (entry + 3) := by
      simpa [s3, State.put, Nat.add_assoc] using next_pc s2 (entry + 2) pc2 (by omega)
    have t0 : programStep program state = some s1 := by
      rw [fetched program state entry (.branchZero 0 (word width returnPc)) position
        (by omega) (by simpa [At, code] using present ⟨0, by decide⟩)]
      have nonzero : (word width (count + 1)).val ≠ 0 := by
        rw [show (word width (count + 1)).val = count + 1 from Nat.mod_eq_of_lt countFits]
        omega
      simp [step, running, countStored, nonzero, s1]
    have t1 : programStep program s1 = some s2 := by
      rw [fetched program s1 (entry + 1) .release pc1 (by omega)
        (by simpa [At, code] using present ⟨1, by decide⟩)]
      have nonempty : state.heap.isEmpty = false := by simp [Array.isEmpty, size]
      simp [step, s1, s2, State.advance, running, nonempty]
    have t2 : programStep program s2 = some s3 := by
      rw [fetched program s2 (entry + 2) (.add 0 0 6) pc2 (by omega)
        (by simpa [At, code] using present ⟨2, by decide⟩)]
      simp only [step, show s2.halted = false from running, Bool.false_eq_true, ↓reduceIte]
      change some (s2.advance.put 0 (word width ((state.reg 0).val + (state.reg 6).val))) = some s3
      rw [countStored, minusStored, decrement count countFits]
    have t3 : programStep program s3 = some s4 := by
      rw [fetched program s3 (entry + 3) (.branchZero 2 (word width entry)) pc3 (by omega)
        (by simpa [At, code] using present ⟨3, by decide⟩)]
      simp [step, s3, s2, s1, State.advance, State.put, running, zeroStored, word, s4]
    have size4 : s4.heap.size = keep + count := by
      simp only [s4, s3, s2, State.advance, State.put, Array.size_pop]
      omega
    have count4 : s4.reg 0 = word width count := by simp [s4, s3, State.advance, State.put]
    have minus4 : s4.reg 6 = word width (2 ^ width - 1) := by
      simpa [s4, s3, s2, s1, State.advance, State.put] using minusStored
    have zero4 : s4.reg 2 = word width 0 := by
      simpa [s4, s3, s2, s1, State.advance, State.put] using zeroStored
    obtain ⟨final, tail, finalSize, finalStack, finalOutput, finalPc, finalRunning, tailFrame⟩ :=
      ih s4 rfl running (by omega) count4 minus4 zero4 size4
    have live1 : s1.liveWords = state.liveWords := rfl
    have live2 : s2.liveWords = s4.liveWords := rfl
    have live3 : s3.liveWords = s4.liveWords := rfl
    have lower : s4.liveWords ≤ state.liveWords := by
      simp only [State.liveWords, s4, s3, s2, s1, State.advance, State.put, Array.size_pop]
      omega
    have loop : Execution program state s4 4 state.liveWords := by
      simpa only [live1, live2, live3, Nat.max_self, Nat.max_eq_left lower, Nat.reduceAdd] using
        Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.refl s4))))
    refine ⟨final, ?_, finalSize, finalStack, finalOutput, finalPc, finalRunning, ?_⟩
    · convert loop.append tail using 1 <;> omega
    · exact ForestZeroBackendFrame.trans
        (ForestZeroBackendFrame.release state.heap (by omega)) tailFrame


/-- The release count is fetched from the actual caller stack. -/
def setupCode (width : Nat) : Program width 8 :=
  #[.pop 0, .constant 6 (word width (2 ^ width - 1)), .constant 2 (word width 0)]

theorem stacked_execution (program : Program width 8) (entry returnPc keep count : Nat)
    (state : State width 8) (rest : List (Word width))
    (setupAt : ∀ phase : Fin 3, program[entry + phase.val]? = (setupCode width)[phase.val]?)
    (loopAt : At program (entry + 3) returnPc)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (saved : state.stack = word width count :: rest) (size : state.heap.size = keep + count) :
    ∃ final, Execution program state final (4 * count + 4) state.liveWords ∧
      final.heap.size = keep ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap := by
  let s1 : State width 8 := { state.advance.put 0 (word width count) with stack := rest }
  let s2 := s1.advance.put 6 (word width (2 ^ width - 1))
  let s3 := s2.advance.put 2 (word width 0)
  have pc1 : s1.pc = word width (entry + 1) := by
    simpa [s1, State.put] using next_pc state entry position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    simpa [s2, State.put, Nat.add_assoc] using next_pc s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    simpa [s3, State.put, Nat.add_assoc] using next_pc s2 (entry + 2) pc2 (by omega)
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry (.pop 0) position (by omega)
      (by simpa [setupCode] using setupAt ⟨0, by decide⟩)]
    simp [step, running, saved, s1]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 6 (word width (2 ^ width - 1))) pc1 (by omega)
      (by simpa [setupCode] using setupAt ⟨1, by decide⟩)]
    simp [step, s1, s2, State.advance, State.put, running]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.constant 2 (word width 0)) pc2 (by omega)
      (by simpa [setupCode] using setupAt ⟨2, by decide⟩)]
    simp [step, s1, s2, s3, State.advance, State.put, running]
  have count3 : s3.reg 0 = word width count := by simp [s3, s2, s1, State.advance, State.put]
  have minus3 : s3.reg 6 = word width (2 ^ width - 1) := by simp [s3, s2, State.advance, State.put]
  have zero3 : s3.reg 2 = word width 0 := by simp [s3, State.put]
  obtain ⟨final, tail, finalSize, finalStack, finalOutput, finalPc, finalRunning, frame⟩ :=
    execution program (entry + 3) returnPc keep count s3 loopAt pc3 running
      (by omega) countFits count3 minus3 zero3 size
  have live1 : s1.liveWords = s3.liveWords := rfl
  have live2 : s2.liveWords = s3.liveWords := rfl
  have lower : s3.liveWords ≤ state.liveWords := by
    simp only [State.liveWords, s3, s2, s1, State.advance, State.put, saved, List.length_cons]
    omega
  have setup : Execution program state s3 3 state.liveWords := by
    simpa only [live1, live2, Nat.max_self, Nat.max_eq_left lower, Nat.reduceAdd] using
      Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl s3)))
  refine ⟨final, ?_, finalSize, finalStack, finalOutput, finalPc, finalRunning, frame⟩
  convert setup.append tail using 1 <;> omega


/-- The release count is calculated from the actual allocation cursor and the
saved retained boundary, using six fetched machine instructions. -/
def captureCode (width : Nat) : Program width 8 :=
  #[.pop 0, .constant 6 (word width (2 ^ width - 1)), .xor 6 0 6,
    .add 6 6 5, .add 0 7 6, .push 0]

private theorem complement_value (keep : Nat) (fits : keep < 2 ^ width) :
    Nat.xor keep (2 ^ width - 1) = 2 ^ width - 1 - keep := by
  have h := congrArg BitVec.toNat (BitVec.xor_allOnes (x := BitVec.ofNat width keep))
  simpa only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits,
    BitVec.toNat_allOnes, BitVec.toNat_not, Nat.xor_eq] using h

private theorem allocation_difference (keep size : Nat)
    (fits : size < 2 ^ width) (retained : keep ≤ size) :
    word width ((word width size).val +
      (word width ((word width (Nat.xor keep (2 ^ width - 1))).val + 1)).val) =
      word width (size - keep) := by
  have positive := Nat.two_pow_pos width
  have keepFits : keep < 2 ^ width := by omega
  have maskFits : 2 ^ width - 1 < 2 ^ width := by omega
  rw [complement_value keep keepFits]
  have complementFits : 2 ^ width - 1 - keep < 2 ^ width := by omega
  rw [show (word width size).val = size from Nat.mod_eq_of_lt fits,
    show (word width (2 ^ width - 1 - keep)).val = 2 ^ width - 1 - keep
      from Nat.mod_eq_of_lt complementFits]
  have sumEq : size + (2 ^ width - 1 - keep + 1) = size - keep + 2 ^ width := by omega
  apply Fin.ext
  simp only [word]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, sumEq, Nat.add_mod_right]

 theorem capture_execution (program : Program width 8) (entry keep : Nat)
    (state : State width 8) (rest : List (Word width))
    (present : ∀ phase : Fin 6, program[entry + phase.val]? = (captureCode width)[phase.val]?)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 6 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (retained : keep ≤ state.heap.size)
    (saved : state.stack = word width keep :: rest)
    (cursor : state.reg 7 = word width state.heap.size)
    (one : state.reg 5 = word width 1) :
    ∃ final, Execution program state final 6 state.liveWords ∧
      final.heap = state.heap ∧
      final.stack = word width (state.heap.size - keep) :: rest ∧
      final.output = state.output ∧ final.pc = word width (entry + 6) ∧
      final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 6 → final.reg register = state.reg register) := by
  let s1 : State width 8 := { state.advance.put 0 (word width keep) with stack := rest }
  let s2 := s1.advance.put 6 (word width (2 ^ width - 1))
  let s3 := s2.advance.put 6 (word width (Nat.xor keep (2 ^ width - 1)))
  let s4 := s3.advance.put 6 (word width ((s3.reg 6).val + 1))
  let s5 := s4.advance.put 0 (word width (state.heap.size - keep))
  let s6 : State width 8 := { s5.advance with stack := word width (state.heap.size - keep) :: rest }
  have pc1 : s1.pc = word width (entry + 1) := by
    simpa [s1, State.put, Nat.add_assoc] using next_pc state (entry + 0) position (by omega)
  have pc2 : s2.pc = word width (entry + 2) := by
    simpa [s2, State.put, Nat.add_assoc] using next_pc s1 (entry + 1) pc1 (by omega)
  have pc3 : s3.pc = word width (entry + 3) := by
    simpa [s3, State.put, Nat.add_assoc] using next_pc s2 (entry + 2) pc2 (by omega)
  have pc4 : s4.pc = word width (entry + 4) := by
    simpa [s4, State.put, Nat.add_assoc] using next_pc s3 (entry + 3) pc3 (by omega)
  have pc5 : s5.pc = word width (entry + 5) := by
    simpa [s5, State.put, Nat.add_assoc] using next_pc s4 (entry + 4) pc4 (by omega)
  have pc6 : s6.pc = word width (entry + 6) := by
    simpa [s6, State.put, Nat.add_assoc] using next_pc s5 (entry + 5) pc5 (by omega)
  have t0 : programStep program state = some s1 := by
    rw [fetched program state (entry + 0) (.pop 0) position (by omega)
      (by simpa [captureCode] using present ⟨0, by decide⟩)]
    simp [step, running, saved, cursor, one, s1, State.advance, State.put, word, Nat.mod_eq_of_lt (show keep < 2 ^ width by omega), Nat.mod_eq_of_lt (show 2 ^ width - 1 < 2 ^ width by have h := Nat.two_pow_pos width; omega)]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) (.constant 6 (word width (2 ^ width - 1))) pc1 (by omega)
      (by simpa [captureCode] using present ⟨1, by decide⟩)]
    simp [step, running, saved, cursor, one, s2, s1, State.advance, State.put, word, Nat.mod_eq_of_lt (show keep < 2 ^ width by omega), Nat.mod_eq_of_lt (show 2 ^ width - 1 < 2 ^ width by have h := Nat.two_pow_pos width; omega)]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) (.xor 6 0 6) pc2 (by omega)
      (by simpa [captureCode] using present ⟨2, by decide⟩)]
    simp [step, running, saved, cursor, one, s3, s2, s1, State.advance, State.put, word, Nat.mod_eq_of_lt (show keep < 2 ^ width by omega), Nat.mod_eq_of_lt (show 2 ^ width - 1 < 2 ^ width by have h := Nat.two_pow_pos width; omega)]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) (.add 6 6 5) pc3 (by omega)
      (by simpa [captureCode] using present ⟨3, by decide⟩)]
    simp [step, running, saved, cursor, one, s4, s3, s2, s1, State.advance, State.put, word, Nat.mod_eq_of_lt (show keep < 2 ^ width by omega), Nat.mod_eq_of_lt (show 2 ^ width - 1 < 2 ^ width by have h := Nat.two_pow_pos width; omega)]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) (.add 0 7 6) pc4 (by omega)
      (by simpa [captureCode] using present ⟨4, by decide⟩)]
    have reg7 : s4.reg 7 = word width state.heap.size := by
      simp [s4, s3, s2, s1, State.advance, State.put, cursor]
    have reg6 : s4.reg 6 = word width ((word width (Nat.xor keep (2 ^ width - 1))).val + 1) := by
      simp [s4, s3, State.advance, State.put]
    simp only [step, show s4.halted = false from running, Bool.false_eq_true, ite_false]
    change some (s4.advance.put 0 (word width ((s4.reg 7).val + (s4.reg 6).val))) = some s5
    rw [reg7, reg6, allocation_difference keep state.heap.size heapFits retained]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) (.push 0) pc5 (by omega)
      (by simpa [captureCode] using present ⟨5, by decide⟩)]
    simp [step, running, saved, cursor, one, s6, s5, s4, s3, s2, s1, State.advance, State.put, word, Nat.mod_eq_of_lt (show keep < 2 ^ width by omega), Nat.mod_eq_of_lt (show 2 ^ width - 1 < 2 ^ width by have h := Nat.two_pow_pos width; omega)]
  have live : s6.liveWords = state.liveWords := by
    simp [s6, s5, s4, s3, s2, s1, State.liveWords, State.advance, State.put, saved]
  have lower : s1.liveWords ≤ state.liveWords := by
    simp [s1, State.liveWords, State.advance, State.put, saved]
  have lower5 : s5.liveWords ≤ state.liveWords := lower
  have trace : Execution program state s6 6 state.liveWords := by
    simpa only [show s1.liveWords = s2.liveWords from rfl,
      show s2.liveWords = s3.liveWords from rfl,
      show s3.liveWords = s4.liveWords from rfl,
      show s4.liveWords = s5.liveWords from rfl, live,
      Nat.max_eq_right lower5, Nat.max_self, Nat.reduceAdd] using
      Execution.cons t0 (Execution.cons t1 (Execution.cons t2
        (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.refl s6))))))
  refine ⟨s6, trace, rfl, rfl, rfl, pc6, running, ?_⟩
  intro register notZero notSix
  simp [s6, s5, s4, s3, s2, s1, State.advance, State.put, notZero, notSix]


/-- Actual captured count followed by physical release, with no supplied
allocation-count premise. The retained boundary is read from the caller stack. -/
theorem capture_reclaim_execution (program : Program width 8) (entry returnPc keep : Nat)
    (state : State width 8) (rest : List (Word width))
    (captureAt : ∀ phase : Fin 6, program[entry + phase.val]? = (captureCode width)[phase.val]?)
    (setupAt : ∀ phase : Fin 3, program[entry + 6 + phase.val]? = (setupCode width)[phase.val]?)
    (loopAt : At program (entry + 6 + 3) returnPc)
    (position : state.pc = word width entry) (running : state.halted = false)
    (capacity : entry + 13 < 2 ^ width) (heapFits : state.heap.size < 2 ^ width)
    (retained : keep ≤ state.heap.size)
    (saved : state.stack = word width keep :: rest)
    (cursor : state.reg 7 = word width state.heap.size)
    (one : state.reg 5 = word width 1) :
    ∃ final, Execution program state final (4 * (state.heap.size - keep) + 10) state.liveWords ∧
      final.heap.size = keep ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width returnPc ∧ final.halted = false ∧
      PrefixFrame keep state.heap final.heap := by
  obtain ⟨middle, capture, sameHeap, savedCount, sameOutput, middlePC, middleRunning, preserved⟩ :=
    capture_execution program entry keep state rest captureAt position running
      (by omega) heapFits retained saved cursor one
  have countFits : state.heap.size - keep < 2 ^ width := by omega
  have allocated : middle.heap.size = keep + (state.heap.size - keep) := by
    rw [sameHeap]
    omega
  obtain ⟨final, release, finalSize, finalStack, finalOutput, finalPC, finalRunning, frame⟩ :=
    stacked_execution program (entry + 6) returnPc keep (state.heap.size - keep) middle rest
      setupAt loopAt middlePC middleRunning (by omega) countFits savedCount allocated
  have live : middle.liveWords = state.liveWords := by
    unfold State.liveWords
    rw [sameHeap, savedCount, sameOutput, saved]
    simp only [List.length_cons]
  refine ⟨final, ?_, finalSize, finalStack, finalOutput.trans sameOutput,
    finalPC, finalRunning, ?_⟩
  · convert capture.append release using 1 <;> (try simp only [live, Nat.max_self]) <;> omega
  · simpa only [sameHeap] using frame

end Controller.Cost.ForestZeroReclaim
