module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Basic.Assignments

@[expose] public section

namespace Controller

/-- Physical image restriction; positive bus count is imposed by the physical model. -/
def Admissible {n : ℕ} (b : ℕ) (t : Channel n) (K : Finset (Channel n)) : Prop :=
  K.Nonempty ∧ (b = 1 → t ∈ K)

@[simp] theorem admissible_one {n : ℕ} (t : Channel n) (K : Finset (Channel n)) :
    Admissible 1 t K ↔ t ∈ K := by
  constructor
  · exact fun h => h.2 rfl
  · exact fun h => ⟨⟨t, h⟩, fun _ => h⟩

theorem admissible_many {n b : ℕ} (hb : 2 ≤ b) (t : Channel n)
    (K : Finset (Channel n)) : Admissible b t K ↔ K.Nonempty := by
  have hne : b ≠ 1 := by omega
  simp [Admissible, hne]

@[simp] theorem admissible_singleton {n b : ℕ} (t : Channel n) :
    Admissible b t {t} := by simp [Admissible]

@[simp] theorem not_admissible_empty {n b : ℕ} (t : Channel n) :
    ¬ Admissible b t ∅ := by simp [Admissible]

end Controller
