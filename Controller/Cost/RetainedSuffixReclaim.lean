module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedGraphReclaim

@[expose] public section

/-! Fetched setup and counted release reclaim an appended suffix while retaining the caller heap. -/
namespace Controller.Cost.RetainedSuffixReclaim
open Controller.Cost.RawTransferLoops Controller.Cost.SharedEvaluationReclaim

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (state : State width 8)
    (entry done : Nat) (retained : Array (Word width)) (values : List (Word width)) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry + 7 < 2 ^ width)
    (heapCount : state.heap = retained ++ values.toArray) (heapFits : values.length < 2 ^ width)
    (physical : CodeAt resident entry (code width entry done values.length)) :
    ∃ final, Execution resident state final (4 * values.length + 4) state.liveWords ∧
      final.heap = retained ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width done ∧ final.halted = false ∧
      final.reg 0 = word width 0 ∧ final.reg 6 = word width 0 ∧
      final.reg 7 = word width (2 ^ width - 1) ∧
      (∀ index : Fin 8, index ≠ 0 → index ≠ 6 → index ≠ 7 → final.reg index = state.reg index) := by
  have all := physical
  unfold code at all
  have setup := RawSharedOrdered.takePrefix resident entry _ _ all
  have tail := RawSharedOrdered.takeSuffix resident entry _ _ all
  have loop : CodeAt resident (entry + 3) (countedReleaseCode width (entry + 3) done) := by
    simpa only [List.size_toArray, List.length_cons, List.length_nil] using tail
  obtain ⟨counted, t₀, pc₀, value₀, heap₀, stack₀, out₀, run₀, frame₀⟩ :=
    constant_execution resident entry values.length 0 state position running (by omega)
      (by simpa using setup ⟨0, by change 0 < 3; decide⟩)
  obtain ⟨zeroed, t₁, pc₁, value₁, heap₁, stack₁, out₁, run₁, frame₁⟩ :=
    constant_execution resident (entry + 1) 0 6 counted pc₀ run₀ (by omega)
      (by simpa using setup ⟨1, by change 1 < 3; decide⟩)
  obtain ⟨ready, t₂, pc₂, value₂, heap₂, stack₂, out₂, run₂, frame₂⟩ :=
    constant_execution resident (entry + 2) (2 ^ width - 1) 7 zeroed
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using pc₁) run₁ (by omega)
      (by simpa using setup ⟨2, by change 2 < 3; decide⟩)
  obtain ⟨final, peak, release, bound, empty, stack, output, pc, active, zero, frame⟩ :=
    SharedGraphReclaim.execution resident (entry + 3) done retained values ready
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using pc₂) run₂ (by omega)
      (by rw [heap₂, heap₁, heap₀]; exact heapCount) heapFits
      (by rw [frame₂ 0 (by decide), frame₁ 0 (by decide)]; exact value₀)
      value₂ (by rw [frame₂ 6 (by decide)]; exact value₁) loop
  have countedLive : counted.liveWords = state.liveWords := by
    simp only [State.liveWords, heap₀, stack₀, out₀]
  have zeroedLive : zeroed.liveWords = state.liveWords := by
    simp only [State.liveWords, heap₁, stack₁, out₁, heap₀, stack₀, out₀]
  have readyLive : ready.liveWords = state.liveWords := by
    simp only [State.liveWords, heap₂, stack₂, out₂, heap₁, stack₁, out₁, heap₀, stack₀, out₀]
  have joined := t₀.append (t₁.append (t₂.append release))
  have ticksEq : 1 + (1 + (1 + (4 * values.length + 1))) = 4 * values.length + 4 := by omega
  have peakEq : max state.liveWords (max counted.liveWords (max zeroed.liveWords peak)) =
      state.liveWords := by simp only [countedLive, zeroedLive, readyLive] at bound ⊢; omega
  rw [ticksEq, peakEq] at joined
  refine ⟨final, joined, empty, stack.trans (stack₂.trans (stack₁.trans stack₀)),
    output.trans (out₂.trans (out₁.trans out₀)), pc, active, zero, ?_, ?_, ?_⟩
  · rw [frame 6 (by decide), frame₂ 6 (by decide)]; exact value₁
  · rw [frame 7 (by decide)]; exact value₂
  · intro index a b c
    rw [frame index a, frame₂ index c, frame₁ index b, frame₀ index a]

end Controller.Cost.RetainedSuffixReclaim
