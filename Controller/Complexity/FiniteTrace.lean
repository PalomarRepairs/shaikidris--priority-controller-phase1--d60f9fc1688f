module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceMachine

@[expose] public section

/-! A deterministic path ending at a halted state cannot revisit any state.
The finite-state bound is used on bounded readable configurations, excluding
write-only output, to bound transducer time and emitted output length. -/
namespace Controller.Complexity.FiniteTrace

inductive Path (step : A → Option A) : A → A → Nat → Prop
  | refl (state) : Path step state state 0
  | cons {state next final ticks} : step state=some next → Path step next final ticks → Path step state final (ticks+1)

theorem length_unique {step : A → Option A} {state first second firstTicks secondTicks}
    (left : Path step state first firstTicks) (right : Path step state second secondTicks)
    (firstHalted : step first=none) (secondHalted : step second=none) : firstTicks=secondTicks := by
  induction left generalizing second secondTicks with
  | refl state =>
    cases right with
    | refl => rfl
    | cons transition rest => simp [firstHalted] at transition
  | @cons state middle first ticks transition rest ih =>
    cases right with
    | refl => simp [secondHalted] at transition
    | @cons _ other second otherTicks otherTransition tail =>
      have same : middle=other := Option.some.inj (transition.symm.trans otherTransition)
      subst other
      exact congrArg (fun n => n+1) (ih tail firstHalted secondHalted)

theorem Path.splitAt {step : A → Option A} {state final ticks}
    (trace : Path step state final ticks) (index : Nat) (bound : index ≤ ticks) :
    ∃ middle, Path step state middle index ∧ Path step middle final (ticks-index) := by
  induction trace generalizing index with
  | refl state =>
    have zero : index=0 := by omega
    subst index
    exact ⟨state,Path.refl _,Path.refl _⟩
  | @cons state next final ticks transition rest ih =>
    cases index with
    | zero => exact ⟨state,Path.refl _,by simpa using Path.cons transition rest⟩
    | succ index =>
      obtain ⟨middle,first,second⟩ := ih index (by omega)
      exact ⟨middle,Path.cons transition first,by simpa using second⟩

theorem ticks_lt_card [Fintype A] {step : A → Option A} {state final ticks}
    (trace : Path step state final ticks) (halted : step final=none) : ticks<Fintype.card A := by
  classical
  let visit (index : Fin (ticks+1)) : A := (trace.splitAt index.val (by omega)).choose
  have suffix (index : Fin (ticks+1)) : Path step (visit index) final (ticks-index.val) :=
    (trace.splitAt index.val (by omega)).choose_spec.2
  have injective : Function.Injective visit := by
    intro first second same
    have left := suffix first
    have right := suffix second
    rw [same] at left
    have rank := length_unique left right halted halted
    apply Fin.ext
    have a := first.isLt
    have b := second.isLt
    omega
  have bound := Fintype.card_le_of_injective visit injective
  simp only [Fintype.card_fin] at bound
  omega

end Controller.Complexity.FiniteTrace
