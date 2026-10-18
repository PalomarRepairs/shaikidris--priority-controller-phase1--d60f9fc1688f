module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.Model

@[expose] public section

namespace Controller.Cost

/-- An arithmetic-only ledger still follows the very same fetched operations.
It cannot assign an unrelated count to a machine state. -/
def arithmeticRun (p : Program width registers) : Nat → State width registers → Option Nat
  | 0, _ => some 0
  | fuel + 1, s =>
      if s.halted then some 0 else do
        let instruction ← p[s.pc.val]?
        let middle ← step instruction s
        let rest ← arithmeticRun p fuel middle
        pure (instruction.arithmeticOps + rest)

/-- Fuel bounds the number of executed instructions. It is not a declared
complexity bound. Reported ticks and peak are obtained from actual transitions. -/
def run (p : Program width registers) : Nat → State width registers →
    Option (State width registers × Nat × Nat)
  | 0, s => some (s, 0, s.liveWords)
  | fuel + 1, s =>
      if s.halted then some (s, 0, s.liveWords) else do
        let middle ← programStep p s
        let (final, ticks, peak) ← run p fuel middle
        pure (final, ticks + 1, max s.liveWords peak)

theorem run_sound (p : Program width registers) (fuel : Nat)
    (s final : State width registers) (ticks peak : Nat)
    (h : run p fuel s = some (final, ticks, peak)) :
    Execution p s final ticks peak := by
  induction fuel generalizing s final ticks peak with
  | zero =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .refl s
  | succ fuel ih =>
      by_cases halted : s.halted = true
      · simp [run, halted] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .refl s
      · have hoff : s.halted = false := Bool.eq_false_iff.mpr halted
        cases transition : programStep p s with
        | none => simp [run, hoff, transition] at h
        | some middle =>
            cases tail : run p fuel middle with
            | none => simp [run, hoff, transition, tail] at h
            | some result =>
                obtain ⟨endState, count, high⟩ := result
                simp [run, hoff, transition, tail] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact .cons transition (ih middle endState count high tail)

theorem Execution.initial_storage_le {p : Program width registers}
    {s final ticks peak} (h : Execution p s final ticks peak) : s.liveWords ≤ peak := by
  cases h with
  | refl => exact le_refl _
  | cons => exact Nat.le_max_left _ _

theorem Execution.final_storage_le {p : Program width registers}
    {s final ticks peak} (h : Execution p s final ticks peak) : final.liveWords ≤ peak := by
  induction h with
  | refl => exact le_refl _
  | cons _ _ ih => exact ih.trans (Nat.le_max_right _ _)

theorem Execution.append {p : Program width registers}
    {s middle final ticks₁ ticks₂ peak₁ peak₂}
    (first : Execution p s middle ticks₁ peak₁)
    (second : Execution p middle final ticks₂ peak₂) :
    Execution p s final (ticks₁ + ticks₂) (max peak₁ peak₂) := by
  induction first with
  | refl =>
      simpa [Nat.max_eq_right second.initial_storage_le] using second
  | cons transition _ ih =>
      have result := Execution.cons transition (ih second)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.max_assoc] using result

theorem run_ticks_le (p : Program width registers) (fuel : Nat)
    (s final : State width registers) (ticks peak : Nat)
    (h : run p fuel s = some (final, ticks, peak)) : ticks ≤ fuel := by
  induction fuel generalizing s final ticks peak with
  | zero => simp [run] at h; omega
  | succ fuel ih =>
      by_cases halted : s.halted = true
      · simp [run, halted] at h; omega
      · have hoff : s.halted = false := Bool.eq_false_iff.mpr halted
        cases transition : programStep p s with
        | none => simp [run, hoff, transition] at h
        | some middle =>
            cases tail : run p fuel middle with
            | none => simp [run, hoff, transition, tail] at h
            | some result =>
                obtain ⟨endState, count, high⟩ := result
                simp [run, hoff, transition, tail] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                have bound := ih middle endState count high tail
                omega

end Controller.Cost
