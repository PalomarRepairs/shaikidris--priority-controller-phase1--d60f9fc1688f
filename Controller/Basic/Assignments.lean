module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.BooleanAlgebra

@[expose] public section

/-! Finite channel assignments. Declared channels include unused channels. -/
namespace Controller

abbrev Channel (n : ℕ) := Fin n
abbrev Assignment (n : ℕ) := Channel n → Bool

def assignmentOfSet {n : ℕ} (K : Finset (Channel n)) : Assignment n :=
  fun i => decide (i ∈ K)

def setOfAssignment {n : ℕ} (a : Assignment n) : Finset (Channel n) :=
  Finset.univ.filter (fun i => a i = true)

@[simp] theorem assignmentOfSet_eq_true {n : ℕ} (K : Finset (Channel n))
    (i : Channel n) : assignmentOfSet K i = true ↔ i ∈ K := by
  simp [assignmentOfSet]

@[simp] theorem mem_setOfAssignment {n : ℕ} (a : Assignment n) (i : Channel n) :
    i ∈ setOfAssignment a ↔ a i = true := by
  simp [setOfAssignment]

@[simp] theorem setOfAssignment_assignmentOfSet {n : ℕ} (K : Finset (Channel n)) :
    setOfAssignment (assignmentOfSet K) = K := by
  ext i
  simp

@[simp] theorem assignmentOfSet_setOfAssignment {n : ℕ} (a : Assignment n) :
    assignmentOfSet (setOfAssignment a) = a := by
  funext i
  cases h : a i <;> simp [assignmentOfSet, setOfAssignment, h]

@[simp] theorem assignmentOfSet_empty {n : ℕ} :
    assignmentOfSet (∅ : Finset (Channel n)) = fun _ => false := by
  funext i
  simp [assignmentOfSet]

@[simp] theorem assignmentOfSet_union {n : ℕ} (K L : Finset (Channel n))
    (i : Channel n) : assignmentOfSet (K ∪ L) i = (assignmentOfSet K i || assignmentOfSet L i) := by
  simp [assignmentOfSet]

@[simp] theorem assignmentOfSet_inter {n : ℕ} (K L : Finset (Channel n))
    (i : Channel n) : assignmentOfSet (K ∩ L) i = (assignmentOfSet K i && assignmentOfSet L i) := by
  simp [assignmentOfSet]

def FixedConsistent {n : ℕ} (T F : Finset (Channel n)) : Prop := Disjoint T F

def ExtendsFixed {n : ℕ} (T F K : Finset (Channel n)) : Prop :=
  T ⊆ K ∧ Disjoint K F

theorem extendsFixed_consistent {n : ℕ} {T F K : Finset (Channel n)}
    (h : ExtendsFixed T F K) : FixedConsistent T F :=
  h.2.mono_left h.1

theorem extendsFixed_self {n : ℕ} {T F : Finset (Channel n)}
    (h : FixedConsistent T F) : ExtendsFixed T F T := ⟨Finset.Subset.refl _, h⟩

theorem exists_extendsFixed_iff {n : ℕ} (T F : Finset (Channel n)) :
    (∃ K, ExtendsFixed T F K) ↔ FixedConsistent T F := by
  constructor
  · rintro ⟨K, h⟩
    exact extendsFixed_consistent h
  · exact fun h => ⟨T, extendsFixed_self h⟩

/-- Restriction turns channels outside the supplied scope off. -/
def restrictAssignment {n : ℕ} (scope : Finset (Channel n)) (a : Assignment n) :
    Assignment n := fun i => if i ∈ scope then a i else false

@[simp] theorem restrictAssignment_in {n : ℕ} (scope : Finset (Channel n))
    (a : Assignment n) {i : Channel n} (hi : i ∈ scope) :
    restrictAssignment scope a i = a i := by simp [restrictAssignment, hi]

@[simp] theorem restrictAssignment_out {n : ℕ} (scope : Finset (Channel n))
    (a : Assignment n) {i : Channel n} (hi : i ∉ scope) :
    restrictAssignment scope a i = false := by simp [restrictAssignment, hi]

theorem restrictAssignment_assignmentOfSet {n : ℕ} (scope K : Finset (Channel n)) :
    restrictAssignment scope (assignmentOfSet K) = assignmentOfSet (K ∩ scope) := by
  funext i
  by_cases hi : i ∈ scope <;> simp [restrictAssignment, assignmentOfSet, hi]

end Controller
