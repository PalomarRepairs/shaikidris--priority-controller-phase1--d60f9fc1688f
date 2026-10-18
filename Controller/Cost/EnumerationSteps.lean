module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedDetectorSteps
public import Controller.Cost.SharedEvaluationReclaim

@[expose] public section

/-! Single-instruction transitions of the eight-register machine, stated with
explicit frames so that straight-line driver blocks compose by `obtain`. -/
namespace Controller.Cost.EnumerationSteps
open Controller.Cost.RawTransferLoops

variable {width : Nat} (program : Program width 8)

theorem live_put (state : State width 8) (index : Fin 8) (value : Word width) :
    (state.advance.put index value).liveWords = state.liveWords := rfl

theorem add_execution (state : State width 8) (entry : Nat) (dst left right : Fin 8)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (present : program[entry]? = some (.add dst left right)) :
    ∃ final, Execution program state final 1 state.liveWords ∧ final.pc = word width (entry + 1) ∧
      final.reg dst = word width ((state.reg left).val + (state.reg right).val) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, index ≠ dst → final.reg index = state.reg index) := by
  let final := state.advance.put dst (word width ((state.reg left).val + (state.reg right).val))
  have stepped : step (.add dst left right) state = some final := by simp [step, running, final]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  rw [show final.liveWords = state.liveWords from rfl, Nat.max_self] at trace
  refine ⟨final, trace, ?_, by simp [final, State.put], rfl, rfl, rfl, running, ?_⟩
  · simpa [final, State.put] using advance_position state position (by omega)
  · intro index other; simp [final, State.put, State.advance, other]

theorem xor_execution (state : State width 8) (entry : Nat) (dst left right : Fin 8)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (present : program[entry]? = some (.xor dst left right)) :
    ∃ final, Execution program state final 1 state.liveWords ∧ final.pc = word width (entry + 1) ∧
      final.reg dst = word width (Nat.xor (state.reg left).val (state.reg right).val) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, index ≠ dst → final.reg index = state.reg index) := by
  let final := state.advance.put dst (word width (Nat.xor (state.reg left).val (state.reg right).val))
  have stepped : step (.xor dst left right) state = some final := by simp [step, running, final]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  rw [show final.liveWords = state.liveWords from rfl, Nat.max_self] at trace
  refine ⟨final, trace, ?_, by simp [final, State.put], rfl, rfl, rfl, running, ?_⟩
  · simpa [final, State.put] using advance_position state position (by omega)
  · intro index other; simp [final, State.put, State.advance, other]

theorem load_execution (state : State width 8) (entry : Nat) (dst address : Fin 8)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (inside : (state.reg address).val < state.heap.size)
    (present : program[entry]? = some (.load dst address)) :
    ∃ final, Execution program state final 1 state.liveWords ∧ final.pc = word width (entry + 1) ∧
      final.reg dst = state.heap[(state.reg address).val] ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, index ≠ dst → final.reg index = state.reg index) := by
  let final := state.advance.put dst state.heap[(state.reg address).val]
  have stepped : step (.load dst address) state = some final := by simp [step, running, final, inside]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  rw [show final.liveWords = state.liveWords from rfl, Nat.max_self] at trace
  refine ⟨final, trace, ?_, by simp [final, State.put], rfl, rfl, rfl, running, ?_⟩
  · simpa [final, State.put] using advance_position state position (by omega)
  · intro index other; simp [final, State.put, State.advance, other]

theorem store_execution (state : State width 8) (entry : Nat) (address source : Fin 8)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (inside : (state.reg address).val < state.heap.size)
    (present : program[entry]? = some (.store address source)) :
    ∃ final, Execution program state final 1 state.liveWords ∧ final.pc = word width (entry + 1) ∧
      final.heap = state.heap.set (state.reg address).val (state.reg source) inside ∧
      final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, final.reg index = state.reg index) := by
  let final : State width 8 := { state.advance with heap := state.heap.set (state.reg address).val (state.reg source) inside }
  have stepped : step (.store address source) state = some final := by simp [step, running, final, inside]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  have live : final.liveWords = state.liveWords := by simp [final, State.liveWords, State.advance]
  rw [live, Nat.max_self] at trace
  refine ⟨final, trace, ?_, rfl, rfl, rfl, running, fun _ => rfl⟩
  simpa [final] using advance_position state position (by omega)

theorem pop_execution (state : State width 8) (entry : Nat) (dst : Fin 8) (value : Word width)
    (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (input : state.stack = value :: rest)
    (present : program[entry]? = some (.pop dst)) :
    ∃ final, Execution program state final 1 state.liveWords ∧ final.pc = word width (entry + 1) ∧
      final.reg dst = value ∧ final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, index ≠ dst → final.reg index = state.reg index) := by
  let final : State width 8 := { state.advance.put dst value with stack := rest }
  have stepped : step (.pop dst) state = some final := by simp [step, running, final, input]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  have live : final.liveWords ≤ state.liveWords := by
    simp [final, State.liveWords, State.advance, State.put, input]
  rw [Nat.max_eq_left live] at trace
  refine ⟨final, trace, ?_, by simp [final, State.put], rfl, rfl, rfl, running, ?_⟩
  · simpa [final, State.put] using advance_position state position (by omega)
  · intro index other; simp [final, State.put, State.advance, other]

theorem push_execution (state : State width 8) (entry : Nat) (source : Fin 8)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (present : program[entry]? = some (.push source)) :
    ∃ final, Execution program state final 1 (state.liveWords + 1) ∧ final.pc = word width (entry + 1) ∧
      final.heap = state.heap ∧ final.stack = state.reg source :: state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, final.reg index = state.reg index) ∧
      final.liveWords = state.liveWords + 1 := by
  let final : State width 8 := { state.advance with stack := state.reg source :: state.stack }
  have stepped : step (.push source) state = some final := by simp [step, running, final]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  have live : final.liveWords = state.liveWords + 1 := by
    simp [final, State.liveWords, State.advance]; omega
  rw [live, Nat.max_eq_right (Nat.le_succ _)] at trace
  refine ⟨final, trace, ?_, rfl, rfl, rfl, running, fun _ => rfl, live⟩
  simpa [final] using advance_position state position (by omega)

theorem emit_execution (state : State width 8) (entry : Nat) (source : Fin 8)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (present : program[entry]? = some (.emit source)) :
    ∃ final, Execution program state final 1 (state.liveWords + 1) ∧ final.pc = word width (entry + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.reg source :: state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, final.reg index = state.reg index) ∧
      final.liveWords = state.liveWords + 1 := by
  let final : State width 8 := { state.advance with output := state.reg source :: state.output }
  have stepped : step (.emit source) state = some final := by simp [step, running, final]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  have live : final.liveWords = state.liveWords + 1 := by
    simp [final, State.liveWords, State.advance]; omega
  rw [live, Nat.max_eq_right (Nat.le_succ _)] at trace
  refine ⟨final, trace, ?_, rfl, rfl, rfl, running, fun _ => rfl, live⟩
  simpa [final] using advance_position state position (by omega)

theorem allocate_execution (state : State width 8) (entry : Nat) (source : Fin 8)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (fits : state.heap.size < 2 ^ width)
    (present : program[entry]? = some (.allocate source)) :
    ∃ final, Execution program state final 1 (state.liveWords + 1) ∧ final.pc = word width (entry + 1) ∧
      final.heap = state.heap.push (state.reg source) ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, final.reg index = state.reg index) ∧
      final.liveWords = state.liveWords + 1 := by
  let final : State width 8 := { state.advance with heap := state.heap.push (state.reg source) }
  have stepped : step (.allocate source) state = some final := by simp [step, running, final, fits]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  have live : final.liveWords = state.liveWords + 1 := by
    simp [final, State.liveWords, State.advance]; omega
  rw [live, Nat.max_eq_right (Nat.le_succ _)] at trace
  refine ⟨final, trace, ?_, rfl, rfl, rfl, running, fun _ => rfl, live⟩
  simpa [final] using advance_position state position (by omega)

theorem branch_taken (state : State width 8) (entry target : Nat) (source : Fin 8)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (zero : (state.reg source).val = 0)
    (present : program[entry]? = some (.branchZero source (word width target))) :
    ∃ final, Execution program state final 1 state.liveWords ∧ final.pc = word width target ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, final.reg index = state.reg index) := by
  let final : State width 8 := { state.advance with pc := word width target }
  have stepped : step (.branchZero source (word width target)) state = some final := by
    simp [step, running, final, zero]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  rw [show final.liveWords = state.liveWords from rfl, Nat.max_self] at trace
  exact ⟨final, trace, rfl, rfl, rfl, rfl, running, fun _ => rfl⟩

theorem branch_skipped (state : State width 8) (entry target : Nat) (source : Fin 8)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (nonzero : (state.reg source).val ≠ 0)
    (present : program[entry]? = some (.branchZero source (word width target))) :
    ∃ final, Execution program state final 1 state.liveWords ∧ final.pc = word width (entry + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, final.reg index = state.reg index) := by
  let final : State width 8 := state.advance
  have stepped : step (.branchZero source (word width target)) state = some final := by
    simp [step, running, final, nonzero]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  rw [show final.liveWords = state.liveWords from rfl, Nat.max_self] at trace
  exact ⟨final, trace, advance_position state position (by omega), rfl, rfl, rfl, running, fun _ => rfl⟩

theorem halt_execution (state : State width 8) (entry : Nat)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 1 < 2 ^ width)
    (present : program[entry]? = some .halt) :
    ∃ final, Execution program state final 1 state.liveWords ∧ final.halted = true ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output := by
  let final : State width 8 := { state.advance with halted := true }
  have stepped : step (.halt) state = some final := by simp [step, running, final]
  have trace := SharedDetectorSteps.single program state final entry _ position (by omega) present stepped
  rw [show final.liveWords = state.liveWords from rfl, Nat.max_self] at trace
  exact ⟨final, trace, rfl, rfl, rfl, rfl⟩

/-- An unconditional jump through register 0. -/
theorem jump_execution (state : State width 8) (entry target : Nat)
    (position : state.pc = word width entry) (running : state.halted = false) (room : entry + 2 < 2 ^ width)
    (first : program[entry]? = some (.constant 0 (word width 0)))
    (second : program[entry + 1]? = some (.branchZero 0 (word width target))) :
    ∃ final, Execution program state final 2 state.liveWords ∧ final.pc = word width target ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.halted = false ∧ (∀ index : Fin 8, index ≠ 0 → final.reg index = state.reg index) := by
  obtain ⟨cleared, clearTrace, clearPC, clearReg, clearHeap, clearStack, clearOutput, clearRunning, clearFrame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry 0 0 state position running (by omega) first
  obtain ⟨final, jumpTrace, finalPC, finalHeap, finalStack, finalOutput, finalRunning, finalFrame⟩ :=
    branch_taken program cleared (entry + 1) target 0 clearPC clearRunning (by omega)
      (by rw [clearReg]; simp [word]) second
  have clearedLive : cleared.liveWords = state.liveWords := by
    simp only [State.liveWords, clearHeap, clearStack, clearOutput]
  have joined := clearTrace.append jumpTrace
  rw [clearedLive, Nat.max_self] at joined
  refine ⟨final, joined, finalPC, finalHeap.trans clearHeap, finalStack.trans clearStack,
    finalOutput.trans clearOutput, finalRunning, fun index other => ?_⟩
  rw [finalFrame, clearFrame index other]

end Controller.Cost.EnumerationSteps
