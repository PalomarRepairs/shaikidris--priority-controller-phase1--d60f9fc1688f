module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Decoder.Enumerate
public import Controller.Cost.SharedRetainedCandidates
public import Controller.Cost.SharedDetectorFeasibility

@[expose] public section

/-! Mask words of an enumeration prefix. The driver keeps the `2n` input-mask
words of the current prefix query in a scratch heap region; every driver step
changes at most two cells. This file proves the cell updates and the bridge
from the oracle decision to the D08 prefix query. -/
namespace Controller.Cost.EnumerationMasks
open Controller.Decoder Controller.Decoder.Enumeration

variable {n : ℕ}

/-- Baseline words for `B`, then one flag word per channel for `F`. -/
def masksOf (width : Nat) (B F : Finset (Channel n)) : List (Word width) :=
  SharedRetainedCandidates.masks width (assignmentOfSet B) ((List.finRange n).map (assignmentOfSet F))

/-- The oracle input of the D08 query on `(fixedTrue d P, fixedFalse d P)`. -/
def maskList (width b : Nat) (t : Channel n) (d : Nat) (P : Finset (Channel n)) : List (Word width) :=
  masksOf width (extensionBase b t (fixedTrue d P)) (fixedFalse d P)

@[simp] theorem masksOf_length (width : Nat) (B F : Finset (Channel n)) :
    (masksOf width B F).length = 2 * n := by
  simp [masksOf, SharedRetainedCandidates.masks]; omega

@[simp] theorem maskList_length (width b : Nat) (t : Channel n) (d : Nat) (P : Finset (Channel n)) :
    (maskList width b t d P).length = 2 * n := masksOf_length _ _ _

theorem masksOf_getElem?_base (width : Nat) (B F : Finset (Channel n)) (c : Channel n) :
    (masksOf width B F)[c.val]? = some (boolWord width (decide (c ∈ B))) := by
  unfold masksOf SharedRetainedCandidates.masks
  rw [List.getElem?_append_left (by simp)]
  simp [assignmentOfSet]

theorem masksOf_getElem?_flag (width : Nat) (B F : Finset (Channel n)) (c : Channel n) :
    (masksOf width B F)[n + c.val]? = some (boolWord width (decide (c ∈ F))) := by
  unfold masksOf SharedRetainedCandidates.masks
  rw [List.getElem?_append_right (by simp)]
  simp [assignmentOfSet]

theorem masksOf_getElem?_high (width : Nat) (B F : Finset (Channel n)) (index : Nat)
    (high : 2 * n ≤ index) : (masksOf width B F)[index]? = none := by
  apply List.getElem?_eq_none
  simpa using high

/-- Two mask lists agree when their baseline and flag sets agree. -/
theorem masksOf_ext (width : Nat) (B F B' F' : Finset (Channel n))
    (base : ∀ c, c ∈ B ↔ c ∈ B') (flag : ∀ c, c ∈ F ↔ c ∈ F') :
    masksOf width B F = masksOf width B' F' := by
  have eB : B = B' := Finset.ext base
  have eF : F = F' := Finset.ext flag
  rw [eB, eF]

/-- Every index is a baseline cell, a flag cell or out of range. -/
theorem index_cases (index : Nat) :
    (∃ c : Channel n, index = c.val) ∨ (∃ c : Channel n, index = n + c.val) ∨ 2 * n ≤ index := by
  by_cases low : index < n
  · exact Or.inl ⟨⟨index, low⟩, rfl⟩
  · by_cases mid : index < 2 * n
    · exact Or.inr (Or.inl ⟨⟨index - n, by omega⟩, by simp; omega⟩)
    · exact Or.inr (Or.inr (by omega))

theorem masksOf_set_base (width : Nat) (B F : Finset (Channel n)) (c : Channel n) (value : Bool) :
    (masksOf width B F).set c.val (boolWord width value) =
      masksOf width (if value then insert c B else B.erase c) F := by
  apply List.ext_getElem?
  intro index
  have cBound := c.isLt
  rw [List.getElem?_set, masksOf_length]
  rcases index_cases (n := n) index with ⟨d, rfl⟩ | ⟨d, rfl⟩ | high
  · rw [masksOf_getElem?_base, masksOf_getElem?_base]
    by_cases same : c = d
    · subst d
      rw [ite_eq_left rfl, ite_eq_left (by omega)]
      cases value <;> simp
    · have different : c.val ≠ d.val := fun h => same (Fin.ext h)
      rw [ite_eq_right different]
      cases value <;> simp [Ne.symm same]
  · have dBound := d.isLt
    rw [masksOf_getElem?_flag, masksOf_getElem?_flag, ite_eq_right (by omega)]
  · rw [masksOf_getElem?_high _ _ _ _ high, masksOf_getElem?_high _ _ _ _ high, ite_eq_right (by omega)]

theorem masksOf_set_flag (width : Nat) (B F : Finset (Channel n)) (c : Channel n) (value : Bool) :
    (masksOf width B F).set (n + c.val) (boolWord width value) =
      masksOf width B (if value then insert c F else F.erase c) := by
  apply List.ext_getElem?
  intro index
  have cBound := c.isLt
  rw [List.getElem?_set, masksOf_length]
  rcases index_cases (n := n) index with ⟨d, rfl⟩ | ⟨d, rfl⟩ | high
  · have dBound := d.isLt
    rw [masksOf_getElem?_base, masksOf_getElem?_base, ite_eq_right (by omega)]
  · rw [masksOf_getElem?_flag, masksOf_getElem?_flag]
    by_cases same : c = d
    · subst d
      rw [ite_eq_left rfl, ite_eq_left (by omega)]
      cases value <;> simp
    · have different : n + c.val ≠ n + d.val := fun h => same (Fin.ext (by omega))
      rw [ite_eq_right different]
      cases value <;> simp [Ne.symm same]
  · rw [masksOf_getElem?_high _ _ _ _ high, masksOf_getElem?_high _ _ _ _ high, ite_eq_right (by omega)]

/-! Prefix sets. -/

theorem mem_fixedTrue (d : Nat) (P : Finset (Channel n)) (c : Channel n) :
    c ∈ fixedTrue d P ↔ c ∈ P ∧ c.val < d := by simp [fixedTrue]

theorem mem_fixedFalse (d : Nat) (P : Finset (Channel n)) (c : Channel n) :
    c ∈ fixedFalse d P ↔ c.val < d ∧ c ∉ P := by simp [fixedFalse]

theorem mem_extensionBase (b : Nat) (t : Channel n) (T : Finset (Channel n)) (c : Channel n) :
    c ∈ extensionBase b t T ↔ (b = 1 ∧ c = t) ∨ c ∈ T := by
  by_cases one : b = 1 <;> simp [extensionBase, one]

/-- A feasible prefix already contains the forced target when it is below the depth. -/
theorem target_fixed (graph : DAG n) (guarded : graph.Guarded) (b : Nat) (t : Channel n)
    (d : Nat) (P : Finset (Channel n)) (feasible : query graph b t true d P = true)
    (one : b = 1) (below : t.val < d) : t ∈ P := by
  obtain ⟨K, detects, agreement⟩ := (query_true_iff graph guarded b t true d P).mp feasible
  have present : t ∈ K := detects.2.1.2 one
  exact (agreement t below).mp present

/-- Consistency of the false-child query of a feasible bounded prefix. -/
theorem false_child_consistent (graph : DAG n) (guarded : graph.Guarded) (b : Nat) (t : Channel n)
    (d : Nat) (P : Finset (Channel n)) (lower : d < n) (bounded : Bounded d P)
    (feasible : query graph b t true d P = true) (free : ¬(b = 1 ∧ t.val = d)) :
    FixedConsistent (extensionBase b t (fixedTrue (d + 1) P)) (fixedFalse (d + 1) P) := by
  unfold FixedConsistent
  rw [Finset.disjoint_left]
  intro c inBase inFalse
  rw [mem_extensionBase, mem_fixedTrue] at inBase
  rw [mem_fixedFalse] at inFalse
  rcases inBase with ⟨one, rfl⟩ | ⟨member, _⟩
  · have below : c.val < d := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp inFalse.1 with h | h
      · exact h
      · exact False.elim (free ⟨one, h⟩)
    exact inFalse.2 (target_fixed graph guarded b c d P feasible one below)
  · exact inFalse.2 member

/-- Consistency of a sibling query built from a detecting previous result. -/
theorem sibling_consistent (b : Nat) (t : Channel n) (c : Nat) (lower : c < n)
    (previous : Finset (Channel n)) (forced : b = 1 → t ∈ previous) :
    FixedConsistent (extensionBase b t (fixedTrue (c + 1) (insert ⟨c, lower⟩ (fixedTrue c previous))))
      (fixedFalse (c + 1) (insert ⟨c, lower⟩ (fixedTrue c previous))) := by
  unfold FixedConsistent
  rw [Finset.disjoint_left]
  intro x inBase inFalse
  rw [mem_extensionBase, mem_fixedTrue] at inBase
  rw [mem_fixedFalse] at inFalse
  rcases inBase with ⟨one, rfl⟩ | ⟨member, _⟩
  · apply inFalse.2
    rcases Nat.lt_succ_iff_lt_or_eq.mp inFalse.1 with h | h
    · exact Finset.mem_insert_of_mem ((mem_fixedTrue _ _ _).mpr ⟨forced one, h⟩)
    · have eq : x = ⟨c, lower⟩ := Fin.ext h
      rw [eq]; exact Finset.mem_insert_self _ _
  · exact inFalse.2 member

theorem initial_consistent (b : Nat) (t : Channel n) :
    FixedConsistent (extensionBase b t (fixedTrue 0 (∅ : Finset (Channel n))))
      (fixedFalse 0 (∅ : Finset (Channel n))) := by
  unfold FixedConsistent
  rw [Finset.disjoint_left]
  intro c _ inFalse
  rw [mem_fixedFalse] at inFalse
  omega

/-- The forced false child is infeasible. -/
theorem forced_query_false (graph : DAG n) (b : Nat) (t : Channel n) (P : Finset (Channel n))
    (one : b = 1) (absent : t ∉ P) : query graph b t true (t.val + 1) P = false := by
  unfold query
  rw [graph.extendSet_conflict]
  · rfl
  · intro consistent
    apply Finset.disjoint_left.mp consistent
      ((mem_extensionBase b t _ t).mpr (Or.inl ⟨one, rfl⟩))
    rw [mem_fixedFalse]
    exact ⟨Nat.lt_succ_self _, absent⟩

/-! Cell updates of the driver. -/

section Updates
variable (width b : Nat) (t : Channel n)

theorem complete_flag (d : Nat) (P : Finset (Channel n)) (lower : d < n) (bounded : Bounded d P) :
    maskList width b t (d + 1) P = (maskList width b t d P).set (n + d) (boolWord width true) := by
  have flag := masksOf_set_flag width (extensionBase b t (fixedTrue d P)) (fixedFalse d P) ⟨d, lower⟩ true
  simp only [ite_true] at flag
  unfold maskList
  rw [flag]
  apply masksOf_ext
  · intro c
    simp only [mem_extensionBase, mem_fixedTrue]
    constructor
    · rintro (h | ⟨member, _⟩)
      · exact Or.inl h
      · exact Or.inr ⟨member, bounded c member⟩
    · rintro (h | ⟨member, below⟩)
      · exact Or.inl h
      · exact Or.inr ⟨member, by omega⟩
  · intro c
    simp only [Finset.mem_insert, mem_fixedFalse]
    constructor
    · rintro ⟨below, absent⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp below with h | h
      · exact Or.inr ⟨h, absent⟩
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | ⟨below, absent⟩)
      · exact ⟨Nat.lt_succ_self _, fun member => Nat.lt_irrefl _ (bounded _ member)⟩
      · exact ⟨by omega, absent⟩

theorem complete_true_child (d : Nat) (P : Finset (Channel n)) (lower : d < n) (bounded : Bounded d P) :
    maskList width b t (d + 1) (insert ⟨d, lower⟩ P) =
      ((maskList width b t (d + 1) P).set (n + d) (boolWord width false)).set d (boolWord width true) := by
  have flag := masksOf_set_flag width (extensionBase b t (fixedTrue (d + 1) P)) (fixedFalse (d + 1) P)
    ⟨d, lower⟩ false
  have base := masksOf_set_base width (extensionBase b t (fixedTrue (d + 1) P))
    ((fixedFalse (d + 1) P).erase ⟨d, lower⟩) ⟨d, lower⟩ true
  simp only [Bool.false_eq_true, ite_false, ite_true] at flag base
  unfold maskList
  rw [flag, base]
  apply masksOf_ext
  · intro c
    simp only [Finset.mem_insert, mem_extensionBase, mem_fixedTrue]
    constructor
    · rintro (h | ⟨rfl | member, below⟩)
      · exact Or.inr (Or.inl h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨member, below⟩)
    · rintro (rfl | h | ⟨member, below⟩)
      · exact Or.inr ⟨Or.inl rfl, Nat.lt_succ_self _⟩
      · exact Or.inl h
      · exact Or.inr ⟨Or.inr member, below⟩
  · intro c
    simp only [Finset.mem_erase, Finset.mem_insert, mem_fixedFalse, not_or]
    constructor
    · rintro ⟨below, different, absent⟩
      exact ⟨different, below, absent⟩
    · rintro ⟨different, below, absent⟩
      exact ⟨below, different, absent⟩

theorem forced_skip (d : Nat) (P : Finset (Channel n)) (lower : d < n) (one : b = 1)
    (target : t.val = d) :
    maskList width b t (d + 1) (insert ⟨d, lower⟩ P) = maskList width b t d P ∨
      ¬Bounded d P := by
  by_cases bounded : Bounded d P
  · left
    have eqT : (⟨d, lower⟩ : Channel n) = t := Fin.ext target.symm
    unfold maskList
    apply masksOf_ext
    · intro c
      simp only [Finset.mem_insert, mem_extensionBase, mem_fixedTrue, one, true_and]
      constructor
      · rintro (h | ⟨h | member, below⟩)
        · exact Or.inl h
        · exact Or.inl (h.trans eqT)
        · exact Or.inr ⟨member, bounded c member⟩
      · rintro (h | ⟨member, below⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr member, by omega⟩
    · intro c
      simp only [Finset.mem_insert, mem_fixedFalse, not_or]
      constructor
      · rintro ⟨below, different, absent⟩
        refine ⟨?_, absent⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp below with h | h
        · exact h
        · exact False.elim (different (Fin.ext h))
      · rintro ⟨below, absent⟩
        exact ⟨by omega, fun h => by subst c; simp at below, absent⟩
  · exact Or.inr bounded

theorem seek_skip_forced (c : Nat) (previous : Finset (Channel n)) (lower : c < n) (one : b = 1)
    (target : t.val = c) :
    maskList width b t (c + 1) (fixedTrue (c + 1) previous) =
      maskList width b t c (fixedTrue c previous) ∨ (⟨c, lower⟩ : Channel n) ∉ previous := by
  by_cases present : (⟨c, lower⟩ : Channel n) ∈ previous
  · left
    have eqT : (⟨c, lower⟩ : Channel n) = t := Fin.ext target.symm
    unfold maskList
    apply masksOf_ext
    · intro x
      simp only [mem_extensionBase, mem_fixedTrue, one, true_and]
      constructor
      · rintro (h | ⟨⟨member, below⟩, _⟩)
        · exact Or.inl h
        · rcases Nat.lt_succ_iff_lt_or_eq.mp below with h | h
          · exact Or.inr ⟨⟨member, h⟩, h⟩
          · exact Or.inl ((Fin.ext h : x = ⟨c, lower⟩).trans eqT)
      · rintro (h | ⟨⟨member, below⟩, _⟩)
        · exact Or.inl h
        · exact Or.inr ⟨⟨member, by omega⟩, by omega⟩
    · intro x
      simp only [mem_fixedFalse, mem_fixedTrue, not_and]
      constructor
      · rintro ⟨below, absent⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp below with h | h
        · exact ⟨h, fun member => by have := absent member; omega⟩
        · have eq : x = ⟨c, lower⟩ := Fin.ext h
          subst x
          exact False.elim (absent present (Nat.lt_succ_self _))
      · rintro ⟨below, absent⟩
        exact ⟨by omega, fun member _ => absent member below⟩
  · exact Or.inr present

theorem seek_skip (c : Nat) (previous : Finset (Channel n)) (lower : c < n)
    (present : (⟨c, lower⟩ : Channel n) ∈ previous) (free : ¬(b = 1 ∧ t.val = c)) :
    maskList width b t c (fixedTrue c previous) =
      (maskList width b t (c + 1) (fixedTrue (c + 1) previous)).set c (boolWord width false) := by
  have base := masksOf_set_base width (extensionBase b t (fixedTrue (c + 1) (fixedTrue (c + 1) previous)))
    (fixedFalse (c + 1) (fixedTrue (c + 1) previous)) ⟨c, lower⟩ false
  simp only [Bool.false_eq_true, ite_false] at base
  unfold maskList
  rw [base]
  apply masksOf_ext
  · intro x
    simp only [Finset.mem_erase, mem_extensionBase, mem_fixedTrue]
    constructor
    · rintro (⟨one, rfl⟩ | ⟨⟨member, below⟩, _⟩)
      · refine ⟨fun h => free ⟨one, by rw [h]⟩, Or.inl ⟨one, rfl⟩⟩
      · exact ⟨fun h => by rw [h] at below; exact Nat.lt_irrefl _ below,
          Or.inr ⟨⟨member, by omega⟩, by omega⟩⟩
    · rintro ⟨different, h | ⟨⟨member, below⟩, _⟩⟩
      · exact Or.inl h
      · rcases Nat.lt_succ_iff_lt_or_eq.mp below with h | h
        · exact Or.inr ⟨⟨member, h⟩, h⟩
        · exact False.elim (different (Fin.ext h))
  · intro x
    simp only [mem_fixedFalse, mem_fixedTrue, not_and]
    constructor
    · rintro ⟨below, absent⟩
      exact ⟨by omega, fun member _ => absent member below⟩
    · rintro ⟨below, absent⟩
      refine ⟨?_, fun member _ => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp below with h | h
        · exact h
        · have eq : x = ⟨c, lower⟩ := Fin.ext h
          subst x
          exact False.elim (absent present (Nat.lt_succ_self _))
      · exact absent member (by omega)

theorem seek_try (c : Nat) (previous : Finset (Channel n)) (lower : c < n)
    (absent : (⟨c, lower⟩ : Channel n) ∉ previous) :
    maskList width b t (c + 1) (insert ⟨c, lower⟩ (fixedTrue c previous)) =
      ((maskList width b t (c + 1) (fixedTrue (c + 1) previous)).set (n + c) (boolWord width false)).set c
        (boolWord width true) := by
  have flag := masksOf_set_flag width (extensionBase b t (fixedTrue (c + 1) (fixedTrue (c + 1) previous)))
    (fixedFalse (c + 1) (fixedTrue (c + 1) previous)) ⟨c, lower⟩ false
  have base := masksOf_set_base width (extensionBase b t (fixedTrue (c + 1) (fixedTrue (c + 1) previous)))
    ((fixedFalse (c + 1) (fixedTrue (c + 1) previous)).erase ⟨c, lower⟩) ⟨c, lower⟩ true
  simp only [Bool.false_eq_true, ite_false, ite_true] at flag base
  unfold maskList
  rw [flag, base]
  apply masksOf_ext
  · intro x
    simp only [Finset.mem_insert, mem_extensionBase, mem_fixedTrue]
    constructor
    · rintro (h | ⟨rfl | ⟨member, below⟩, _⟩)
      · exact Or.inr (Or.inl h)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨⟨member, by omega⟩, by omega⟩)
    · rintro (rfl | h | ⟨⟨member, below⟩, _⟩)
      · exact Or.inr ⟨Or.inl rfl, Nat.lt_succ_self _⟩
      · exact Or.inl h
      · rcases Nat.lt_succ_iff_lt_or_eq.mp below with h | h
        · exact Or.inr ⟨Or.inr ⟨member, h⟩, by omega⟩
        · exact Or.inr ⟨Or.inl (Fin.ext h), by omega⟩
  · intro x
    simp only [Finset.mem_erase, Finset.mem_insert, mem_fixedFalse, mem_fixedTrue, not_or, not_and]
    constructor
    · rintro ⟨below, different, absentX⟩
      exact ⟨different, below, fun member _ => absentX member (by
        rcases Nat.lt_succ_iff_lt_or_eq.mp below with h | h
        · exact h
        · exact False.elim (different (Fin.ext h)))⟩
    · rintro ⟨different, below, absentX⟩
      exact ⟨below, different, fun member _ => absentX member below⟩

theorem seek_fail (c : Nat) (previous : Finset (Channel n)) (lower : c < n)
    (absent : (⟨c, lower⟩ : Channel n) ∉ previous) (free : ¬(b = 1 ∧ t.val = c)) :
    maskList width b t c (fixedTrue c previous) =
      (maskList width b t (c + 1) (insert ⟨c, lower⟩ (fixedTrue c previous))).set c (boolWord width false) := by
  have base := masksOf_set_base width
    (extensionBase b t (fixedTrue (c + 1) (insert ⟨c, lower⟩ (fixedTrue c previous))))
    (fixedFalse (c + 1) (insert ⟨c, lower⟩ (fixedTrue c previous))) ⟨c, lower⟩ false
  simp only [Bool.false_eq_true, ite_false] at base
  unfold maskList
  rw [base]
  apply masksOf_ext
  · intro x
    have xLower := x.isLt
    simp only [Finset.mem_erase, Finset.mem_insert, mem_extensionBase, mem_fixedTrue, ne_eq, Fin.ext_iff] at free absent ⊢
    by_cases m : x ∈ previous <;> by_cases e : x.val = c <;> by_cases tx : x = t <;>
      simp only [m, e, tx, Fin.ext_iff] at * <;> grind
  · intro x
    simp only [Finset.mem_insert, mem_fixedFalse, mem_fixedTrue, Fin.ext_iff]
    by_cases m : x ∈ previous <;> by_cases e : x.val = c <;> simp only [m, e] <;> grind

/-- The baseline cell read by the sibling scan. -/
theorem seek_read (c : Nat) (previous : Finset (Channel n)) (lower : c < n)
    (forced : b = 1 → t ∈ previous) :
    (maskList width b t (c + 1) (fixedTrue (c + 1) previous))[c]? =
      some (boolWord width (decide ((⟨c, lower⟩ : Channel n) ∈ previous))) := by
  unfold maskList
  have cell := masksOf_getElem?_base width (extensionBase b t (fixedTrue (c + 1) (fixedTrue (c + 1) previous)))
    (fixedFalse (c + 1) (fixedTrue (c + 1) previous)) ⟨c, lower⟩
  refine cell.trans ?_
  congr 2
  apply decide_eq_decide.mpr
  simp only [mem_extensionBase, mem_fixedTrue]
  constructor
  · rintro (⟨one, h⟩ | ⟨⟨member, _⟩, _⟩)
    · rw [h]; exact forced one
    · exact member
  · intro member
    exact Or.inr ⟨⟨member, Nat.lt_succ_self _⟩, Nat.lt_succ_self _⟩

theorem fixedTrue_full (K : Finset (Channel n)) : fixedTrue n K = K := by
  ext c; simp [fixedTrue, c.isLt]

theorem bounded_full (K : Finset (Channel n)) : Bounded n K := fun c _ => c.isLt

/-- A completed result is stored with its own baseline words. -/
theorem result_baseline (K : Finset (Channel n)) (forced : b = 1 → t ∈ K) (c : Channel n) :
    (maskList width b t n K)[c.val]? = some (boolWord width (decide (c ∈ K))) := by
  unfold maskList
  rw [masksOf_getElem?_base, fixedTrue_full]
  congr 2
  apply decide_eq_decide.mpr
  simp only [mem_extensionBase]
  constructor
  · rintro (⟨one, rfl⟩ | member)
    · exact forced one
    · exact member
  · exact Or.inr

theorem seek_start (K : Finset (Channel n)) :
    maskList width b t n (fixedTrue n K) = maskList width b t n K := by
  rw [fixedTrue_full]

end Updates

/-! Oracle decision bridge. -/

theorem atRoot_iff_query (parameters : Native.Parameters) (graph : DAG parameters.channels)
    (guarded : graph.Guarded) (d : Nat) (P : Finset (Channel parameters.channels)) :
    (∃ output : Fin graph.roots.length,
      Cost.SharedDetectorFeasibility.AtRoot parameters graph (fixedTrue d P) (fixedFalse d P) output) ↔
      query graph parameters.buses parameters.bridge.target true d P = true := by
  have optionIff : query graph parameters.buses parameters.bridge.target true d P = true ↔
      ∃ K, graph.extendSet parameters.buses parameters.bridge.target true (fixedTrue d P)
        (fixedFalse d P) = some K := by
    unfold query
    cases graph.extendSet parameters.buses parameters.bridge.target true (fixedTrue d P)
      (fixedFalse d P) <;> simp
  rw [optionIff, graph.extendSet_exists_iff guarded]
  constructor
  · rintro ⟨output, K, eligible, fixed, differs⟩
    exact ⟨rfl, graph.roots[output.val], List.getElem_mem _, K, eligible, fixed, Ne.symm differs⟩
  · rintro ⟨_, root, present, K, eligible, fixed, differs⟩
    obtain ⟨index, bound, eq⟩ := List.getElem_of_mem present
    refine ⟨⟨index, bound⟩, K, eligible, fixed, ?_⟩
    simp only [eq]
    exact Ne.symm differs

end Controller.Cost.EnumerationMasks
