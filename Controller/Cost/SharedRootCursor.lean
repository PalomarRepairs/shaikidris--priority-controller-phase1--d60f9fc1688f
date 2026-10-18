module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedQuerySourceFrame

@[expose] public section

namespace Controller.Cost.SharedRootCursor
open Controller.Cost.GateProgram Controller.Cost.RawTransferLoops

def code (width exhausted : Nat) : Program width 8 :=
  #[.pop 3, .pop 0, .branchZero 0 (word width exhausted),
    .constant 6 (word width (2 ^ width - 1)), .add 0 0 6, .push 0,
    .constant 0 (word width 1), .add 0 3 0, .push 0, .constant 0 (word width 0)]

@[simp] theorem code_size : (code width exhausted).size = 10 := rfl

private theorem decrement (count : Nat) (fits : count + 1 < 2 ^ width) :
    word width ((word width (count + 1)).val + (word width (2 ^ width - 1)).val) = word width count := by
  have positive : 0 < 2 ^ width := Nat.two_pow_pos width
  have minusFits : 2 ^ width - 1 < 2 ^ width := by omega
  rw [show (word width (count + 1)).val = count + 1 from Nat.mod_eq_of_lt fits,
    show (word width (2 ^ width - 1)).val = 2 ^ width - 1 from Nat.mod_eq_of_lt minusFits]
  have sum : count + 1 + (2 ^ width - 1) = count + 2 ^ width := by omega
  simp only [sum, word, Nat.add_mod_right]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem successor_execution (program : Program width 8) (state : State width 8)
    (entry exhausted source count : Nat) (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry + 10 < 2 ^ width) (countFits : count + 1 < 2 ^ width)
    (sourceFits : source < 2 ^ width)
    (input : state.stack = word width source :: word width (count + 1) :: rest)
    (physical : CodeAt program entry (code width exhausted)) :
    ∃ final, Execution program state final 10 state.liveWords ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      final.stack = word width (source + 1) :: word width count :: rest ∧
      final.pc = word width (entry + 10) ∧ final.halted = false ∧
      final.reg 0 = word width 0 ∧ final.reg 3 = word width source ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 3 → index ≠ 6 → final.reg index = state.reg index) := by
  let s0 := state
  let s1 := { (s0.advance.put 3 (word width source)) with stack := word width (count + 1) :: rest }
  let s2 := { (s1.advance.put 0 (word width (count + 1))) with stack := rest }
  let s3 := s2.advance
  let s4 := s3.advance.put 6 (word width (2 ^ width - 1))
  let s5 := s4.advance.put 0 (word width count)
  let s6 := { s5.advance with stack := word width count :: rest }
  let s7 := s6.advance.put 0 (word width 1)
  let s8 := s7.advance.put 0 (word width (source + 1))
  let s9 := { s8.advance with stack := word width (source + 1) :: word width count :: rest }
  let s10 := s9.advance.put 0 (word width 0)
  have countValue : (word width (count + 1)).val = count + 1 := Nat.mod_eq_of_lt countFits
  have sourceValue : (word width source).val = source := Nat.mod_eq_of_lt sourceFits
  have oneValue : (word width 1).val = 1 := Nat.mod_eq_of_lt (by omega)
  have minusValue : (word width (2 ^ width - 1)).val = 2 ^ width - 1 :=
    Nat.mod_eq_of_lt (by have := Nat.two_pow_pos width; omega)
  have decrementRaw : word width (count + 1 + (2 ^ width - 1)) = word width count := by
    simpa only [countValue, minusValue] using decrement count countFits
  have p0 : s0.pc = word width entry := position
  have p1 : s1.pc = word width (entry + 1) := by
    simpa only [s1, State.put, Nat.add_assoc, Nat.reduceAdd] using
      advance_position s0 p0 (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using
      advance_position s1 p1 (by omega)
  have p3 : s3.pc = word width (entry + 3) := by
    simpa only [s3, State.put, Nat.add_assoc, Nat.reduceAdd] using
      advance_position s2 p2 (by omega)
  have p4 : s4.pc = word width (entry + 4) := by
    simpa only [s4, State.put, Nat.add_assoc, Nat.reduceAdd] using
      advance_position s3 p3 (by omega)
  have p5 : s5.pc = word width (entry + 5) := by
    simpa only [s5, State.put, Nat.add_assoc, Nat.reduceAdd] using
      advance_position s4 p4 (by omega)
  have p6 : s6.pc = word width (entry + 6) := by
    simpa only [s6, State.put, Nat.add_assoc, Nat.reduceAdd] using
      advance_position s5 p5 (by omega)
  have p7 : s7.pc = word width (entry + 7) := by
    simpa only [s7, State.put, Nat.add_assoc, Nat.reduceAdd] using
      advance_position s6 p6 (by omega)
  have p8 : s8.pc = word width (entry + 8) := by
    simpa only [s8, State.put, Nat.add_assoc, Nat.reduceAdd] using
      advance_position s7 p7 (by omega)
  have p9 : s9.pc = word width (entry + 9) := by
    simpa only [s9, State.put, Nat.add_assoc, Nat.reduceAdd] using
      advance_position s8 p8 (by omega)
  have p10 : s10.pc = word width (entry + 10) := by
    simpa only [s10, State.put, Nat.add_assoc, Nat.reduceAdd] using
      advance_position s9 p9 (by omega)
  have t0 : programStep program s0 = some s1 := by
    rw [fetched program s0 (entry + 0) _ (by simpa using p0) (by omega)
      (by simpa [code] using physical ⟨0, by simp⟩)]
    simp [step, running, s0, s1, State.advance, State.put, input]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) _ (by simpa using p1) (by omega)
      (by simpa [code] using physical ⟨1, by simp⟩)]
    simp [step, running, s0, s1, s2, State.advance, State.put]
  have t2 : programStep program s2 = some s3 := by
    rw [fetched program s2 (entry + 2) _ (by simpa using p2) (by omega)
      (by simpa [code] using physical ⟨2, by simp⟩)]
    simp [step, running, s0, s1, s2, s3, State.advance, State.put, countValue]
  have t3 : programStep program s3 = some s4 := by
    rw [fetched program s3 (entry + 3) _ (by simpa using p3) (by omega)
      (by simpa [code] using physical ⟨3, by simp⟩)]
    simp [step, running, s0, s1, s2, s3, s4, State.advance, State.put]
  have t4 : programStep program s4 = some s5 := by
    rw [fetched program s4 (entry + 4) _ (by simpa using p4) (by omega)
      (by simpa [code] using physical ⟨4, by simp⟩)]
    simp [step, running, s0, s1, s2, s3, s4, s5, State.advance, State.put, countValue, minusValue, decrementRaw]
  have t5 : programStep program s5 = some s6 := by
    rw [fetched program s5 (entry + 5) _ (by simpa using p5) (by omega)
      (by simpa [code] using physical ⟨5, by simp⟩)]
    simp [step, running, s0, s1, s2, s3, s4, s5, s6, State.advance, State.put]
  have t6 : programStep program s6 = some s7 := by
    rw [fetched program s6 (entry + 6) _ (by simpa using p6) (by omega)
      (by simpa [code] using physical ⟨6, by simp⟩)]
    simp [step, running, s0, s1, s2, s3, s4, s5, s6, s7, State.advance, State.put]
  have t7 : programStep program s7 = some s8 := by
    rw [fetched program s7 (entry + 7) _ (by simpa using p7) (by omega)
      (by simpa [code] using physical ⟨7, by simp⟩)]
    simp [step, running, s0, s1, s2, s3, s4, s5, s6, s7, s8, State.advance, State.put, sourceValue, oneValue]
  have t8 : programStep program s8 = some s9 := by
    rw [fetched program s8 (entry + 8) _ (by simpa using p8) (by omega)
      (by simpa [code] using physical ⟨8, by simp⟩)]
    simp [step, running, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, State.advance, State.put]
  have t9 : programStep program s9 = some s10 := by
    rw [fetched program s9 (entry + 9) _ (by simpa using p9) (by omega)
      (by simpa [code] using physical ⟨9, by simp⟩)]
    simp [step, running, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put]
  have joined := (Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.cons t3 (Execution.cons t4 (Execution.cons t5 (Execution.cons t6 (Execution.cons t7 (Execution.cons t8 (Execution.cons t9 (Execution.refl (p := program) s10)))))))))))
  refine ⟨s10, ?_, rfl, rfl, rfl, p10, running, rfl, ?_, ?_⟩
  · convert joined using 1
    simp only [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.liveWords, State.advance, State.put, input,
      List.length_cons]
    omega
  · simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put]
  · intro index notZero notThree notSix
    simp [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, State.advance, State.put, notZero, notThree, notSix]

open Controller.Cost.ForestZeroAdmissibleCaller

theorem successor_ready (program : Program width 8) (state : State width 8)
    (sourceHeap : Array (Word width)) (tableBase inverseBase entry exhausted source count : Nat)
    (rest : List (Word width))
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry
      (word width source :: word width (count + 1) :: rest) state)
    (room : entry + 10 < 2 ^ width) (countFits : count + 1 < 2 ^ width)
    (sourceFits : source < 2 ^ width) (physical : CodeAt program entry (code width exhausted)) :
    ∃ final, Execution program state final 10 state.liveWords ∧
      final.heap = state.heap ∧ final.output = state.output ∧ final.reg 3 = word width source ∧
      QueryReady (ambient := ambient) sourceHeap tableBase inverseBase (entry + 10)
        (word width (source + 1) :: word width count :: rest) final := by
  obtain ⟨final, trace, heap, output, stack, pc, active, zero, pointer, frame⟩ :=
    successor_execution program state entry exhausted source count rest ready.position ready.running
      room countFits sourceFits ready.stack physical
  refine ⟨final, trace, heap, output, pointer, ?_⟩
  exact ⟨by rw [heap]; exact ready.heapSize,
    by rw [heap]; exact ready.sourceFrame,
    by rw [heap]; exact ready.zeroTable,
    stack, pc, active, zero,
    (frame 1 (by decide) (by decide) (by decide)).trans ready.tableRegister,
    (frame 2 (by decide) (by decide) (by decide)).trans ready.inverseRegister⟩

set_option maxRecDepth 4096 in
theorem zero_ready (program : Program width 8) (state : State width 8)
    (sourceHeap : Array (Word width)) (tableBase inverseBase entry exhausted source : Nat)
    (rest : List (Word width))
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry
      (word width source :: word width 0 :: rest) state)
    (room : entry + 10 < 2 ^ width) (physical : CodeAt program entry (code width exhausted)) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.output = state.output ∧
      QueryReady (ambient := ambient) sourceHeap tableBase inverseBase exhausted rest final := by
  let s1 := { state.advance.put 3 (word width source) with stack := word width 0 :: rest }
  let s2 := { s1.advance.put 0 (word width 0) with stack := rest }
  let final := { s2.advance with pc := word width exhausted }
  have p1 : s1.pc = word width (entry + 1) := by
    simpa only [s1, State.put] using advance_position state ready.position (by omega)
  have p2 : s2.pc = word width (entry + 2) := by
    simpa only [s2, State.put, Nat.add_assoc, Nat.reduceAdd] using advance_position s1 p1 (by omega)
  have t0 : programStep program state = some s1 := by
    rw [fetched program state entry _ ready.position (by omega)
      (by simpa [code] using physical ⟨0, by simp⟩)]
    simp [step, ready.running, ready.stack, s1]
  have t1 : programStep program s1 = some s2 := by
    rw [fetched program s1 (entry + 1) _ p1 (by omega)
      (by simpa [code] using physical ⟨1, by simp⟩)]
    simp [step, s1, s2, State.advance, State.put, ready.running]
  have t2 : programStep program s2 = some final := by
    rw [fetched program s2 (entry + 2) _ p2 (by omega)
      (by simpa [code] using physical ⟨2, by simp⟩)]
    simp [step, s1, s2, State.advance, State.put, ready.running, word, final]
  have trace := Execution.cons t0 (Execution.cons t1 (Execution.cons t2 (Execution.refl (p := program) final)))
  refine ⟨final, ?_, rfl, rfl, ?_⟩
  · convert trace using 1
    simp only [s1, s2, final, State.liveWords, State.advance, State.put, ready.stack, List.length_cons]
    omega
  · refine ⟨ready.heapSize, ready.sourceFrame, ready.zeroTable, rfl, rfl, ready.running, ?_, ?_, ?_⟩
    · simp [final, s2, s1, State.advance, State.put]
    · simpa [final, s2, s1, State.advance, State.put] using ready.tableRegister
    · simpa [final, s2, s1, State.advance, State.put] using ready.inverseRegister

theorem zero_halts (program : Program width 8) (state : State width 8)
    (sourceHeap : Array (Word width)) (tableBase inverseBase entry exhausted source : Nat)
    (rest : List (Word width))
    (ready : QueryReady (ambient := ambient) sourceHeap tableBase inverseBase entry
      (word width source :: word width 0 :: rest) state)
    (room : entry + 10 < 2 ^ width) (physical : CodeAt program entry (code width exhausted))
    (exhaustedRoom : exhausted + 2 < 2 ^ width)
    (exhaustedAt : ∀ phase : Fin 2,
      program[exhausted + phase.val]? = (ForestZeroRootLoop.exhaustedCode width)[phase.val]?) :
    ∃ final, Execution program state final 5 state.liveWords ∧
      final.halted = true ∧ final.reg 4 = word width 0 ∧
      final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output := by
  obtain ⟨stopped, cursorTrace, heap, output, stoppedReady⟩ :=
    zero_ready program state sourceHeap tableBase inverseBase entry exhausted source rest ready room physical
  have finish := ForestZeroRootLoop.exhausted_execution program stopped exhausted
    stoppedReady.position stoppedReady.running exhaustedRoom exhaustedAt
  have stoppedBound : stopped.liveWords ≤ state.liveWords := by
    simp only [State.liveWords, heap, output, stoppedReady.stack, ready.stack, List.length_cons]
    omega
  refine ⟨ForestZeroRootLoop.exhaustedState stopped exhausted, ?_, rfl, ?_, heap, stoppedReady.stack, output⟩
  · simpa only [Nat.max_eq_left stoppedBound, Nat.reduceAdd] using cursorTrace.append finish
  · simp [ForestZeroRootLoop.exhaustedState, State.put]

end Controller.Cost.SharedRootCursor
