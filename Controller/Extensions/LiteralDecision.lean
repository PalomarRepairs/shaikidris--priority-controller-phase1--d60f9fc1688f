module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.LiteralWitness
public import Controller.Extensions.LiteralScan

@[expose] public section

/-! The per-root decision in the shape executed by the machine: a few
first-hit scans and constant work. A result is a two-form descriptor:
the positive literals with the forced target, or one channel with it. -/
namespace Controller.Extensions.LiteralDecision
open Controller.Decoder Controller.Extensions.GateBasis Controller.Extensions.LiteralMachine
open Controller.Extensions.LiteralWitness Controller.Extensions.LiteralScan

variable {n : ℕ}

inductive Descriptor (n : ℕ) where
  | keep
  | single (channel : Channel n)

def Descriptor.set (b : ℕ) (target : Channel n) (a : Raw n) : Descriptor n → Finset (Channel n)
  | .keep => a.positive ∪ forced b target
  | .single c => {c} ∪ forced b target

/-- Scan predicates over channel indices. -/
def posBit (a : Raw n) (c : ℕ) : Bool := if h : c < n then decide (⟨c, h⟩ ∈ a.positive) else false
def negBit (a : Raw n) (c : ℕ) : Bool := if h : c < n then decide (⟨c, h⟩ ∈ a.negative) else false

theorem firstHit_bound (hit : ℕ → Bool) (c k d : ℕ) (h : firstHit hit c k = some d) : d < c + k :=
  (firstHit_some hit k c d h).2.1

/-- Promote a scan result below `n` to a channel. -/
def toChannel (d : Option ℕ) : Option (Channel n) :=
  match d with
  | some d => if h : d < n then some ⟨d, h⟩ else none
  | none => none

theorem firstHit_eq_find (hit : ℕ → Bool) : ∀ k c, firstHit hit c k = (List.range' c k).find? hit := by
  intro k
  induction k with
  | zero => intro c; rfl
  | succ k ih =>
    intro c
    rw [List.range'_succ, List.find?_cons, firstHit, ih]
    cases hit c <;> rfl

theorem toChannel_find (f : Channel n → Bool) (g : ℕ → Bool)
    (agree : ∀ c : Channel n, g c.val = f c) :
    toChannel (n := n) (firstHit g 0 n) = (List.finRange n).find? f := by
  rw [firstHit_eq_find, ← List.range_eq_range', ← List.map_coe_finRange_eq_range, List.find?_map]
  have same : (g ∘ Fin.val) = f := funext agree
  rw [same]
  cases h : (List.finRange n).find? f with
  | none => rfl
  | some c => simp [toChannel, c.isLt]

theorem firstHit_none_iff (hit : ℕ → Bool) (c k : ℕ) :
    firstHit hit c k = none ↔ ∀ e, c ≤ e → e < c + k → hit e = false := by
  constructor
  · exact firstHit_none hit k c
  · intro all
    cases h : firstHit hit c k with
    | none => rfl
    | some d =>
      obtain ⟨low, high, value, _⟩ := firstHit_some hit k c d h
      rw [all d low high] at value
      exact absurd value (by decide)

theorem posBit_channel (a : Raw n) (c : Channel n) : posBit a c.val = decide (c ∈ a.positive) := by
  simp [posBit, c.isLt]

theorem negBit_channel (a : Raw n) (c : Channel n) : negBit a c.val = decide (c ∈ a.negative) := by
  simp [negBit, c.isLt]

/-- No positive literal outside the target. -/
theorem healthy_positive (a : Raw n) (target : Channel n) :
    ((firstHit (posBit a) 0 target.val).isNone && (firstHit (posBit a) (target.val + 1) (n - target.val - 1)).isNone)
      = true ↔ a.positive ⊆ {target} := by
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, firstHit_none_iff]
  constructor
  · rintro ⟨below, above⟩ c member
    have bit : posBit a c.val = true := by rw [posBit_channel]; simpa using member
    rcases lt_trichotomy c.val target.val with lt | eq | gt
    · rw [below c.val (Nat.zero_le _) (by omega)] at bit; exact absurd bit (by decide)
    · exact Finset.mem_singleton.mpr (Fin.ext eq)
    · have := c.isLt
      rw [above c.val (by omega) (by omega)] at bit; exact absurd bit (by decide)
  · intro subset
    have none : ∀ e (h : e < n), e ≠ target.val → posBit a e = false := by
      intro e h different
      have : (⟨e, h⟩ : Channel n) ∉ a.positive := fun member =>
        different (congrArg Fin.val (Finset.mem_singleton.mp (subset member)))
      simp [posBit, h, this]
    refine ⟨fun e _ high => none e (by have := target.isLt; omega) (by omega), fun e low high => ?_⟩
    by_cases h : e < n
    · exact none e h (by omega)
    · simp [posBit, h]

theorem healthy_iff (a : Raw n) (target : Channel n) :
    (!a.zero && (firstHit (posBit a) 0 target.val).isNone &&
      (firstHit (posBit a) (target.val + 1) (n - target.val - 1)).isNone && !negBit a target.val) = true ↔
      Holds a.decode {target} := by
  rw [holds_iff]
  have positive := healthy_positive a target
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at positive ⊢
  rw [negBit_channel, Finset.disjoint_singleton_right]
  constructor
  · rintro ⟨⟨⟨zero, below⟩, above⟩, neg⟩
    exact ⟨zero, positive.mp ⟨below, above⟩, by simpa using neg⟩
  · rintro ⟨zero, subset, neg⟩
    exact ⟨⟨⟨zero, (positive.mpr subset).1⟩, (positive.mpr subset).2⟩, by simpa using neg⟩

def decision (b : ℕ) (target : Channel n) (a : Raw n) : Option (Descriptor n) :=
  let healthy := !a.zero && (firstHit (posBit a) 0 target.val).isNone &&
    (firstHit (posBit a) (target.val + 1) (n - target.val - 1)).isNone && !negBit a target.val
  if healthy then
    match toChannel (n := n) (firstHit (negBit a) 0 n) with
    | some m => some (.single m)
    | none =>
      if room : b ≠ 1 ∧ posBit a target.val = true ∧ 2 ≤ n then
        some (.single ⟨if target.val = 0 then 1 else 0, by have := room.2.2; split <;> omega⟩)
      else none
  else if a.zero then none
  else if (firstHit (fun c => posBit a c && negBit a c) 0 n).isSome || (b == 1 && negBit a target.val) then none
  else if b = 1 ∨ (firstHit (posBit a) 0 n).isSome then some .keep
  else (toChannel (n := n) (firstHit (fun c => !negBit a c) 0 n)).map .single

theorem forced_empty (b : ℕ) (target : Channel n) (notOne : b ≠ 1) : forced b target = ∅ := by
  simp [forced, notOne]

theorem isSome_firstHit_iff (hit : ℕ → Bool) (c k : ℕ) :
    (firstHit hit c k).isSome = true ↔ ∃ e, c ≤ e ∧ e < c + k ∧ hit e = true := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨low, high, value, _⟩ := firstHit_some hit k c d hd
    exact ⟨d, low, high, value⟩
  · rintro ⟨e, low, high, value⟩
    cases r : firstHit hit c k with
    | none => rw [firstHit_none hit k c r e low high] at value; exact absurd value (by decide)
    | some _ => rfl

theorem anyPos_iff (a : Raw n) : (firstHit (posBit a) 0 n).isSome = true ↔ a.positive.Nonempty := by
  rw [isSome_firstHit_iff]
  constructor
  · rintro ⟨e, _, high, value⟩
    have h : e < n := by omega
    exact ⟨⟨e, h⟩, by simpa [posBit, h] using value⟩
  · rintro ⟨c, member⟩
    exact ⟨c.val, Nat.zero_le _, by simpa using c.isLt, by simp [posBit, c.isLt, member]⟩

theorem conflict_iff (a : Raw n) :
    (firstHit (fun c => posBit a c && negBit a c) 0 n).isSome = true ↔ ¬Disjoint a.positive a.negative := by
  rw [isSome_firstHit_iff, Finset.not_disjoint_iff]
  constructor
  · rintro ⟨e, _, high, value⟩
    have h : e < n := by omega
    simp only [posBit, negBit, h, dite_eq_left, Bool.and_eq_true, decide_eq_true_eq] at value
    exact ⟨⟨e, h⟩, value.1, value.2⟩
  · rintro ⟨c, pos, neg⟩
    exact ⟨c.val, Nat.zero_le _, by simpa using c.isLt, by simp [posBit, negBit, c.isLt, pos, neg]⟩

theorem find_inside (P : Finset (Channel n)) (target : Channel n) (subset : P ⊆ {target}) :
    (List.finRange n).find? (fun p => decide (p ∈ P)) = if target ∈ P then some target else none := by
  by_cases present : target ∈ P
  · rw [ite_eq_left present]
    cases r : (List.finRange n).find? (fun p => decide (p ∈ P)) with
    | none =>
      have := List.find?_eq_none.mp r target (List.mem_finRange target)
      simp [present] at this
    | some y =>
      have chosen : y ∈ P := by simpa using List.find?_some r
      rw [Finset.mem_singleton.mp (subset chosen)]
  · rw [ite_eq_right present]
    apply List.find?_eq_none.mpr
    intro y _ member
    have inside : y ∈ P := by simpa using member
    rw [Finset.mem_singleton.mp (subset inside)] at inside
    exact present inside

theorem find_other (target : Channel n) :
    (List.finRange n).find? (fun c => decide (c ≠ target)) =
      if room : 2 ≤ n then some ⟨if target.val = 0 then 1 else 0, by split <;> omega⟩ else none := by
  by_cases room : 2 ≤ n
  · rw [dite_eq_left room]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [List.finRange_succ, List.find?_cons]
    by_cases zero : target.val = 0
    · have same : (0 : Fin (m + 2)) = target := Fin.ext zero.symm
      simp only [same, ne_eq, not_true_eq_false, decide_false]
      rw [List.finRange_succ, List.map_cons, List.find?_cons]
      have other : Fin.succ (0 : Fin (m + 1)) ≠ target := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp only [other, ne_eq, not_false_eq_true, decide_true]
      congr 1
      apply Fin.ext
      simp [zero]
    · have other : (0 : Fin (m + 2)) ≠ target := by
        intro h; exact zero (congrArg Fin.val h).symm
      simp only [other, ne_eq, not_false_eq_true, decide_true]
      congr 1
      apply Fin.ext
      simp [zero]
  · rw [dite_eq_right room]
    apply List.find?_eq_none.mpr
    intro c _
    have := c.isLt
    have := target.isLt
    simp only [ne_eq, decide_eq_true_eq, Decidable.not_not]
    exact Fin.ext (by omega)

theorem decision_set (b : ℕ) (target : Channel n) (a : Raw n) :
    (decision b target a).map (Descriptor.set b target a) = rootWitness b target a := by
  have negFind := toChannel_find (fun c => decide (c ∈ a.negative)) (negBit a) (negBit_channel a)
  have freeFind := toChannel_find (fun c => decide (c ∉ a.negative)) (fun c => !negBit a c)
    (fun c => by simp [negBit_channel])
  unfold decision rootWitness
  dsimp only
  by_cases healthy : Holds a.decode {target}
  · have flag := (healthy_iff a target).mpr healthy
    rw [ite_eq_left flag]
    simp only [healthy, decide_true, ite_true]
    obtain ⟨zero, subset, _⟩ := (holds_iff a {target}).mp healthy
    unfold zeroWitness
    simp only [zero, Bool.false_eq_true, ite_false]
    rw [negFind]
    cases hm : (List.finRange n).find? (fun c => decide (c ∈ a.negative)) with
    | some m => simp [Descriptor.set]
    | none =>
      simp only
      by_cases one : b = 1
      · have none : (List.finRange n).find? (fun p => decide (p ∈ a.positive ∧ p ≠ target)) = none := by
          apply List.find?_eq_none.mpr
          intro p _ h
          have h' := of_decide_eq_true h
          exact h'.2 (Finset.mem_singleton.mp (subset h'.1))
        simp [one, none]
        all_goals intro x member; exact Finset.mem_singleton.mp (subset member)
      · rw [find_inside a.positive target subset]
        have posVal : posBit a target.val = decide (target ∈ a.positive) := posBit_channel a target
        by_cases present : target ∈ a.positive
        · simp only [present, ite_true]
          rw [find_other target]
          by_cases room : 2 ≤ n
          · simp [one, present, room, posVal, Descriptor.set, forced_empty b target one]
          · simp [one, present, room, posVal]
        · simp [one, present, posVal]
  · have flag : (!a.zero && (firstHit (posBit a) 0 target.val).isNone &&
        (firstHit (posBit a) (target.val + 1) (n - target.val - 1)).isNone && !negBit a target.val) = false := by
      simpa using mt (healthy_iff a target).mp healthy
    rw [ite_eq_right (by simp [flag])]
    simp only [healthy, decide_false, Bool.false_eq_true, ite_false]
    unfold oneWitness
    by_cases zero : a.zero = true
    · simp [zero]
    · simp only [zero, Bool.false_eq_true, ite_false]
      have disjointIff : Disjoint a.negative (a.positive ∪ forced b target) ↔
          Disjoint a.positive a.negative ∧ ¬(b = 1 ∧ target ∈ a.negative) := by
        rw [Finset.disjoint_union_right, disjoint_comm]
        apply and_congr_right
        intro _
        by_cases one : b = 1 <;> simp [forced, one]
      by_cases clash : Disjoint a.negative (a.positive ∪ forced b target)
      · obtain ⟨separate, targetFree⟩ := disjointIff.mp clash
        have noConflict : (firstHit (fun c => posBit a c && negBit a c) 0 n).isSome = false := by
          simpa using mt (conflict_iff a).mp (not_not.mpr separate)
        have noTarget : (b == 1 && negBit a target.val) = false := by
          by_cases one : b = 1
          · simp [one, negBit_channel]; exact fun h => targetFree ⟨one, h⟩
          · simp [one]
        rw [ite_eq_right (by simp [noConflict, noTarget]), ite_eq_left clash]
        have nonemptyIff : (a.positive ∪ forced b target).Nonempty ↔
            b = 1 ∨ (firstHit (posBit a) 0 n).isSome = true := by
          rw [anyPos_iff, Finset.union_nonempty]
          by_cases one : b = 1
          · simp [forced, one]
          · simp [forced, one]
        by_cases full : (a.positive ∪ forced b target).Nonempty
        · rw [ite_eq_left (nonemptyIff.mp full), ite_eq_left full]
          rfl
        · rw [ite_eq_right (mt nonemptyIff.mpr full), ite_eq_right full]
          have notOne : b ≠ 1 := fun one => full (nonemptyIff.mpr (Or.inl one))
          rw [freeFind, Option.map_map]
          cases (List.finRange n).find? (fun c => decide (c ∉ a.negative)) with
          | none => rfl
          | some c => simp [Descriptor.set, forced_empty b target notOne]
      · rw [ite_eq_right clash]
        have trigger : ((firstHit (fun c => posBit a c && negBit a c) 0 n).isSome ||
            (b == 1 && negBit a target.val)) = true := by
          by_cases separate : Disjoint a.positive a.negative
          · have targetHit : b = 1 ∧ target ∈ a.negative := by
              by_contra no; exact clash (disjointIff.mpr ⟨separate, no⟩)
            simp [targetHit.1, negBit_channel, targetHit.2]
          · simp [(conflict_iff a).mpr separate]
        rw [ite_eq_left trigger]
        rfl

end Controller.Extensions.LiteralDecision
