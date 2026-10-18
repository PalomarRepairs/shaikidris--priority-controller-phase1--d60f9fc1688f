module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedDetectorLoop

@[expose] public section

/-! Straight-line control used to enter the shared detector loop: an output-count guard and
the register/stack handoff that names the candidate directory and the reserved query tables. -/
namespace Controller.Cost.SharedDetectorSteps
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

theorem single (program : Program width 8) (state next : State width 8) (entry : Nat)
    (instruction : Instruction width 8) (position : state.pc = word width entry)
    (fits : entry < 2 ^ width) (present : program[entry]? = some instruction)
    (stepped : step instruction state = some next) :
    Execution program state next 1 (max state.liveWords next.liveWords) := by
  have transition : programStep program state = some next := by
    rw [fetched program state entry instruction position fits present]
    exact stepped
  simpa only [Nat.zero_add] using Execution.cons transition (Execution.refl next)

theorem push_execution (program : Program width 8) (state : State width 8) (entry : Nat) (source : Fin 8)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 1 < 2 ^ width) (present : program[entry]? = some (.push source)) :
    ∃ final, Execution program state final 1 (state.liveWords + 1) ∧
      final.pc = word width (entry + 1) ∧ final.reg = state.reg ∧ final.heap = state.heap ∧
      final.stack = state.reg source :: state.stack ∧ final.output = state.output ∧ final.halted = false := by
  let final : State width 8 := { state.advance with stack := state.reg source :: state.stack }
  have stepped : step (.push source) state = some final := by simp [step, running, final]
  have trace := single program state final entry _ position (by omega) present stepped
  have live : final.liveWords = state.liveWords + 1 := by
    simp only [final, State.liveWords, State.advance, List.length_cons]; omega
  refine ⟨final, ?_, advance_position state position (by omega), rfl, rfl, rfl, rfl, running⟩
  simpa only [live, Nat.max_eq_right (Nat.le_succ _)] using trace

/-- A zero output count halts with the negative decision tag; otherwise control jumps to the
candidate pass. Only register 0 changes on the nonempty path. -/
def guardCode (width entry : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width 4), .load 0 0, .branchZero 0 (word width (entry + 5)),
    .constant 0 (word width 0), .branchZero 0 (word width (entry + 7)),
    .constant 4 (word width 0), .halt]

@[simp] theorem guardCode_length : (guardCode width entry).length = 7 := rfl

theorem guard_execution (program : Program width 8) (state : State width 8) (entry count : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 7 < 2 ^ width) (countFits : count < 2 ^ width)
    (countCell : state.heap[4]? = some (word width count))
    (present : SharedRootRead.BlockAt program entry (guardCode width entry)) :
    ∃ final, Execution program state final 5 state.liveWords ∧ final.heap = state.heap ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      (count = 0 → final.halted = true ∧ final.reg 4 = word width 0) ∧
      (count ≠ 0 → final.halted = false ∧ final.pc = word width (entry + 7) ∧
        ∀ index : Fin 8, index ≠ 0 → final.reg index = state.reg index) := by
  have fetch : ∀ offset (valid : offset < 7), program[entry + offset]? = (guardCode width entry)[offset]? :=
    fun offset valid => present offset (by simpa using valid)
  obtain ⟨addressed, addressTrace, addressPC, addressReg, addressHeap, addressStack, addressOutput,
    addressRunning, addressFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry 4 0 state position running (by omega)
      (by simpa [guardCode] using fetch 0 (by decide))
  have bounded : (addressed.reg 0).val < addressed.heap.size := by
    rw [addressReg, addressHeap]
    have := (Array.getElem?_eq_some_iff.mp countCell).1
    simpa [word, Nat.mod_eq_of_lt (show 4 < 2 ^ width by omega)] using this
  have loadedValue : addressed.heap[(addressed.reg 0).val] = word width count := by
    have cell := countCell
    rw [← addressHeap] at cell
    have index : (addressed.reg 0).val = 4 := by
      rw [addressReg]; exact Nat.mod_eq_of_lt (by omega)
    simp only [index] at bounded ⊢
    rw [Array.getElem?_eq_getElem bounded] at cell
    exact Option.some.inj cell
  let loaded := addressed.advance.put 0 (word width count)
  have loadStep : step (.load 0 0) addressed = some loaded := by
    simp [step, addressRunning, bounded, loaded, loadedValue]
  have loadTrace := single program addressed loaded (entry + 1) _ addressPC (by omega)
    (by simpa [guardCode] using fetch 1 (by decide)) loadStep
  have loadedPC : loaded.pc = word width (entry + 2) := by
    simpa [loaded, State.put] using advance_position addressed addressPC (by omega)
  have addressLive : addressed.liveWords = state.liveWords := by
    simp only [State.liveWords, addressHeap, addressStack, addressOutput]
  have loadedLive : loaded.liveWords = state.liveWords := by
    simp only [loaded, State.liveWords, State.put, State.advance] at addressLive ⊢; exact addressLive
  have branchFetch : program[entry + 2]? = some (.branchZero 0 (word width (entry + 5))) := by
    simpa [guardCode] using fetch 2 (by decide)
  have countValue : (loaded.reg 0).val = count := by
    simp [loaded, State.put, State.advance, word, Nat.mod_eq_of_lt countFits]
  have loadedRunning : loaded.halted = false := addressRunning
  by_cases empty : count = 0
  · let jumped : State width 8 := { loaded.advance with pc := word width (entry + 5) }
    have branchStep : step (.branchZero 0 (word width (entry + 5))) loaded = some jumped := by
      simp [step, loadedRunning, jumped, countValue, empty]
    have branchTrace := single program loaded jumped (entry + 2) _ loadedPC (by omega) branchFetch branchStep
    obtain ⟨tagged, tagTrace, tagPC, tagReg, tagHeap, tagStack, tagOutput, tagRunning, tagFrame⟩ :=
      SharedEvaluationReclaim.constant_execution program (entry + 5) 0 4 jumped rfl loadedRunning (by omega)
        (by simpa [guardCode] using fetch 5 (by decide))
    let final : State width 8 := { tagged.advance with halted := true }
    have haltStep : step .halt tagged = some final := by simp [step, tagRunning, final]
    have haltTrace := single program tagged final (entry + 6) _ (by simpa [Nat.add_assoc] using tagPC) (by omega)
      (by simpa [guardCode] using fetch 6 (by decide)) haltStep
    have jumpedLive : jumped.liveWords = state.liveWords := loadedLive
    have taggedLive : tagged.liveWords = state.liveWords := by
      simp only [State.liveWords, tagHeap, tagStack, tagOutput] at jumpedLive ⊢; exact jumpedLive
    have finalLive : final.liveWords = state.liveWords := taggedLive
    have joined := addressTrace.append (loadTrace.append (branchTrace.append (tagTrace.append haltTrace)))
    simp only [addressLive, loadedLive, jumpedLive, taggedLive, finalLive, Nat.max_self] at joined
    refine ⟨final, joined, ?_, ?_, ?_, fun _ => ⟨rfl, tagReg⟩, fun nonzero => absurd empty nonzero⟩
    · change tagged.heap = state.heap; rw [tagHeap]; exact addressHeap
    · change tagged.stack = state.stack; rw [tagStack]; exact addressStack
    · change tagged.output = state.output; rw [tagOutput]; exact addressOutput
  · let skipped := loaded.advance
    have branchStep : step (.branchZero 0 (word width (entry + 5))) loaded = some skipped := by
      simp [step, loadedRunning, skipped, countValue, empty]
    have branchTrace := single program loaded skipped (entry + 2) _ loadedPC (by omega) branchFetch branchStep
    have skippedPC : skipped.pc = word width (entry + 3) := advance_position loaded loadedPC (by omega)
    obtain ⟨cleared, clearTrace, clearPC, clearReg, clearHeap, clearStack, clearOutput, clearRunning, clearFrame⟩ :=
      SharedEvaluationReclaim.constant_execution program (entry + 3) 0 0 skipped skippedPC loadedRunning (by omega)
        (by simpa [guardCode] using fetch 3 (by decide))
    let final : State width 8 := { cleared.advance with pc := word width (entry + 7) }
    have clearValue : (cleared.reg 0).val = 0 := by rw [clearReg]; simp [word]
    have jumpStep : step (.branchZero 0 (word width (entry + 7))) cleared = some final := by
      simp [step, clearRunning, final, clearValue]
    have jumpTrace := single program cleared final (entry + 4) _ (by simpa [Nat.add_assoc] using clearPC) (by omega)
      (by simpa [guardCode] using fetch 4 (by decide)) jumpStep
    have skippedLive : skipped.liveWords = state.liveWords := loadedLive
    have clearedLive : cleared.liveWords = state.liveWords := by
      simp only [State.liveWords, clearHeap, clearStack, clearOutput] at skippedLive ⊢; exact skippedLive
    have finalLive : final.liveWords = state.liveWords := clearedLive
    have joined := addressTrace.append (loadTrace.append (branchTrace.append (clearTrace.append jumpTrace)))
    simp only [addressLive, loadedLive, skippedLive, clearedLive, finalLive, Nat.max_self] at joined
    refine ⟨final, joined, ?_, ?_, ?_, fun zero => absurd zero empty, fun _ => ⟨clearRunning, rfl, ?_⟩⟩
    · change cleared.heap = state.heap; rw [clearHeap]; exact addressHeap
    · change cleared.stack = state.stack; rw [clearStack]; exact addressStack
    · change cleared.output = state.output; rw [clearOutput]; exact addressOutput
    · intro index other
      change cleared.reg index = state.reg index
      rw [clearFrame index other]
      simp only [skipped, loaded, State.put, State.advance, ite_eq_right other]
      exact addressFrame index other

/-- Registers 0, 1 and 2 receive the zero constant and the two reserved table bases; the
stack receives the candidate-directory address above the output count. -/
def handoffCode (width tableBase inverseBase count source : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width 0), .constant 1 (word width tableBase), .constant 2 (word width inverseBase),
    .constant 3 (word width count), .push 3, .constant 3 (word width source), .push 3]

@[simp] theorem handoffCode_length : (handoffCode width tableBase inverseBase count source).length = 7 := rfl

theorem handoff_execution (program : Program width 8) (state : State width 8)
    (entry tableBase inverseBase count source : Nat)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 7 < 2 ^ width)
    (present : SharedRootRead.BlockAt program entry (handoffCode width tableBase inverseBase count source)) :
    ∃ final peak, Execution program state final 7 peak ∧ peak ≤ state.liveWords + 2 ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      final.stack = word width source :: word width count :: state.stack ∧
      final.pc = word width (entry + 7) ∧ final.halted = false ∧
      final.reg 0 = word width 0 ∧ final.reg 1 = word width tableBase ∧
      final.reg 2 = word width inverseBase := by
  have fetch : ∀ offset (valid : offset < 7), program[entry + offset]? =
      (handoffCode width tableBase inverseBase count source)[offset]? :=
    fun offset valid => present offset (by simpa using valid)
  obtain ⟨s0, t0, pc0, r0, h0, k0, o0, run0, f0⟩ :=
    SharedEvaluationReclaim.constant_execution program entry 0 0 state position running (by omega)
      (by simpa [handoffCode] using fetch 0 (by decide))
  obtain ⟨s1, t1, pc1, r1, h1, k1, o1, run1, f1⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1) tableBase 1 s0 pc0 run0 (by omega)
      (by simpa [handoffCode] using fetch 1 (by decide))
  obtain ⟨s2, t2, pc2, r2, h2, k2, o2, run2, f2⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1 + 1) inverseBase 2 s1 pc1 run1 (by omega)
      (by simpa [handoffCode, Nat.add_assoc] using fetch 2 (by decide))
  obtain ⟨s3, t3, pc3, r3, h3, k3, o3, run3, f3⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1 + 1 + 1) count 3 s2 pc2 run2 (by omega)
      (by simpa [handoffCode, Nat.add_assoc] using fetch 3 (by decide))
  obtain ⟨s4, t4, pc4, r4, h4, k4, o4, run4⟩ :=
    push_execution program s3 (entry + 1 + 1 + 1 + 1) 3 pc3 run3 (by omega)
      (by simpa [handoffCode, Nat.add_assoc] using fetch 4 (by decide))
  obtain ⟨s5, t5, pc5, r5, h5, k5, o5, run5, f5⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry + 1 + 1 + 1 + 1 + 1) source 3 s4 pc4 run4 (by omega)
      (by simpa [handoffCode, Nat.add_assoc] using fetch 5 (by decide))
  obtain ⟨s6, t6, pc6, r6, h6, k6, o6, run6⟩ :=
    push_execution program s5 (entry + 1 + 1 + 1 + 1 + 1 + 1) 3 pc5 run5 (by omega)
      (by simpa [handoffCode, Nat.add_assoc] using fetch 6 (by decide))
  have l0 : s0.liveWords = state.liveWords := by simp only [State.liveWords, h0, k0, o0]
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords, h1, k1, o1] at l0 ⊢; exact l0
  have l2 : s2.liveWords = state.liveWords := by simp only [State.liveWords, h2, k2, o2] at l1 ⊢; exact l1
  have l3 : s3.liveWords = state.liveWords := by simp only [State.liveWords, h3, k3, o3] at l2 ⊢; exact l2
  have l4 : s4.liveWords = state.liveWords + 1 := by
    simp only [State.liveWords, h4, k4, o4, List.length_cons] at l3 ⊢; omega
  have l5 : s5.liveWords = state.liveWords + 1 := by simp only [State.liveWords, h5, k5, o5] at l4 ⊢; exact l4
  have joined := t0.append (t1.append (t2.append (t3.append (t4.append (t5.append t6)))))
  simp only [l0, l1, l2, l3, l4, l5] at joined
  refine ⟨s6, _, joined, ?_, ?_, ?_, ?_, ?_, run6, ?_, ?_, ?_⟩
  · simp only [max_le_iff]; omega
  · rw [h6, h5, h4, h3, h2, h1, h0]
  · rw [o6, o5, o4, o3, o2, o1, o0]
  · rw [k6, k5, r5, k4, k3, r3, k2, k1, k0]
  · simpa only [Nat.add_assoc, Nat.reduceAdd] using pc6
  · rw [r6, f5 0 (by decide), r4, f3 0 (by decide), f2 0 (by decide), f1 0 (by decide), r0]
  · rw [r6, f5 1 (by decide), r4, f3 1 (by decide), f2 1 (by decide), r1]
  · rw [r6, f5 2 (by decide), r4, f3 2 (by decide), r2]

end Controller.Cost.SharedDetectorSteps
