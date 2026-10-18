module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedFilteredProbe

@[expose] public section

/-! Runtime head comparison and increment drive the reused candidate program. -/
namespace Controller.Cost.SharedHeadControl
open Controller.Cost.RawTransferLoops

def header (width entry done channels : Nat) : Program width 8 :=
  #[.constant 0 (word width channels), .xor 0 0 4, .branchZero 0 (word width done)]

def tail (width loop : Nat) : Program width 8 :=
  #[.constant 0 (word width 1), .add 4 4 0, .constant 0 (word width 0), .branchZero 0 (word width loop)]

@[simp] theorem header_size (width entry done channels : Nat) : (header width entry done channels).size = 3 := rfl
@[simp] theorem tail_size (width loop : Nat) : (tail width loop).size = 4 := rfl

private theorem xor_zero_iff (left right : Nat) : Nat.xor left right = 0 ↔ right = left := by
  constructor
  · intro equal
    have derived := congrArg (fun value => Nat.xor left value) equal
    simpa [← Nat.xor_assoc] using derived
  · intro equal; subst right; simp

theorem header_execution (resident : Program width 8) (state : State width 8)
    (entry done channels head : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 3 < 2 ^ width)
    (channelsFit : channels < 2 ^ width) (headFits : head < 2 ^ width)
    (held : state.reg 4 = word width head)
    (physical : CodeAt resident entry (header width entry done channels)) :
    ∃ final, Execution resident state final 3 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if head = channels then done else entry + 3) ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → final.reg register = state.reg register) := by
  obtain ⟨counted, firstTrace, countedPC, countedValue, heap, stack, output, active, frame⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry channels 0 state position running (by omega)
      (by simpa [header] using physical ⟨0, by simp [header]⟩)
  let tested := counted.advance.put 0 (word width (Nat.xor channels head))
  have testStep : programStep resident counted = some tested := by
    rw [fetched resident counted (entry + 1) _ countedPC (by omega)
      (show resident[entry + 1]? = some (.xor 0 0 4) by simpa [header] using physical ⟨1, by simp [header]⟩)]
    simp [step, active, countedValue, (frame 4 (by decide)).trans held,
      show (word width channels).val = channels from Nat.mod_eq_of_lt channelsFit,
      show (word width head).val = head from Nat.mod_eq_of_lt headFits, tested]
  have testedPC : tested.pc = word width (entry + 2) := by
    simpa [tested, State.put, Nat.add_assoc] using advance_position counted countedPC (by omega)
  let final := if head = channels then { tested.advance with pc := word width done } else tested.advance
  have lastStep : programStep resident tested = some final := by
    rw [fetched resident tested (entry + 2) _ testedPC (by omega)
      (show resident[entry + 2]? = some (.branchZero 0 (word width done)) by simpa [header] using physical ⟨2, by simp [header]⟩)]
    have checked : (tested.reg 0).val = 0 ↔ head = channels := by
      change Nat.xor channels head % 2 ^ width = 0 ↔ head = channels
      have xorFit : Nat.xor channels head < 2 ^ width := Nat.xor_lt_two_pow channelsFit headFits
      rw [Nat.mod_eq_of_lt xorFit]
      exact xor_zero_iff channels head
    simp only [step, show tested.halted = false from active, Bool.false_eq_true, ite_false, checked]
    rfl
  have countedLive : counted.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  have testedLive : tested.liveWords = state.liveWords := countedLive
  have finalLive : final.liveWords = state.liveWords := by
    dsimp [final]
    split <;> exact countedLive
  have rest := Execution.cons testStep (Execution.cons lastStep (Execution.refl final))
  have joined := firstTrace.append rest
  rw [countedLive, testedLive, finalLive, Nat.max_self] at joined
  refine ⟨final, by simpa using joined, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [final]; split <;> exact heap
  · dsimp [final]; split <;> exact stack
  · dsimp [final]; split <;> exact output
  · dsimp [final]
    split
    · rfl
    · simpa only [Nat.add_assoc, Nat.reduceAdd] using advance_position tested testedPC (by omega)
  · dsimp [final]; split <;> exact active
  · intro register different
    dsimp [final]
    split <;> simp only [tested, State.advance, State.put, different, ite_false] <;> exact frame register different


theorem tail_execution (resident : Program width 8) (state : State width 8)
    (entry loop head : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 4 < 2 ^ width)
    (headFits : head + 1 < 2 ^ width) (held : state.reg 4 = word width head)
    (physical : CodeAt resident entry (tail width loop)) :
    ∃ final, Execution resident state final 4 state.liveWords ∧
      final.reg 4 = word width (head + 1) ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width loop ∧ final.halted = false ∧
      (∀ register : Fin 8, register ≠ 0 → register ≠ 4 → final.reg register = state.reg register) := by
  obtain ⟨one, firstTrace, onePC, oneValue, heap, stack, output, active, frame⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry 1 0 state position running (by omega)
      (by simpa [tail] using physical ⟨0, by simp [tail]⟩)
  let incremented := one.advance.put 4 (word width (head + 1))
  have addStep : programStep resident one = some incremented := by
    rw [fetched resident one (entry + 1) _ onePC (by omega)
      (show resident[entry + 1]? = some (.add 4 4 0) by simpa [tail] using physical ⟨1, by simp [tail]⟩)]
    simp [step, active, oneValue, (frame 4 (by decide)).trans held,
      show (word width head).val = head from Nat.mod_eq_of_lt (by omega),
      show (word width 1).val = 1 from Nat.mod_eq_of_lt (by omega), incremented]
  have incrementedPC : incremented.pc = word width (entry + 2) := by
    simpa [incremented, State.put, Nat.add_assoc] using advance_position one onePC (by omega)
  obtain ⟨zeroed, zeroTrace, zeroPC, zeroValue, zeroHeap, zeroStack, zeroOutput, zeroRunning, zeroFrame⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry + 2) 0 0 incremented incrementedPC active (by omega)
      (by simpa [tail] using physical ⟨2, by simp [tail]⟩)
  let final := { zeroed.advance with pc := word width loop }
  have jumpStep : programStep resident zeroed = some final := by
    rw [fetched resident zeroed (entry + 3) _
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using zeroPC) (by omega)
      (show resident[entry + 3]? = some (.branchZero 0 (word width loop)) by simpa [tail] using physical ⟨3, by simp [tail]⟩)]
    simp [step, zeroRunning, zeroValue, word, final]
  have oneLive : one.liveWords = state.liveWords := by simp only [State.liveWords, heap, stack, output]
  have incrementedLive : incremented.liveWords = state.liveWords := oneLive
  have zeroLive : zeroed.liveWords = state.liveWords := by
    simp only [State.liveWords, zeroHeap, zeroStack, zeroOutput]; exact oneLive
  have finalLive : final.liveWords = state.liveWords := zeroLive
  have addTrace := Execution.cons addStep (Execution.refl incremented)
  have jumpTrace := Execution.cons jumpStep (Execution.refl final)
  have joined := firstTrace.append (addTrace.append (zeroTrace.append jumpTrace))
  rw [oneLive, incrementedLive, zeroLive, finalLive, Nat.max_self] at joined
  refine ⟨final, by simpa using joined, ?_, zeroHeap.trans heap, zeroStack.trans stack,
    zeroOutput.trans output, rfl, zeroRunning, ?_⟩
  · rw [show final.reg 4 = zeroed.reg 4 from rfl, zeroFrame 4 (by decide)]
    simp [incremented, State.put]
  · intro register different0 different4
    rw [show final.reg register = zeroed.reg register from rfl, zeroFrame register different0]
    simp only [incremented, State.advance, State.put, different4, ite_false]
    exact frame register different0

end Controller.Cost.SharedHeadControl
