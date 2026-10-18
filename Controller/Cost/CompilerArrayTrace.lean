module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.CompilerPrefixTrace

@[expose] public section

/-! Actual list-to-array recursion records each push and preserves the supplied
array prefix. Counts are source recursion/push calls; backing-array allocation
and fetched RAM compiler refinement are separate. -/
namespace Controller.Cost.CompilerArrayTrace

inductive Trace {α : Type} : List α → Array α → Array α → Nat → Prop
  | nil (initial : Array α) : Trace [] initial initial 0
  | cons (head : α) (rest : List α) (initial result : Array α) (count : Nat)
      (next : Trace rest (initial.push head) result count) :
      Trace (head :: rest) initial result (count + 1)

@[simp] theorem arrayAux_nil (initial : Array α) : ([] : List α).toArrayAux initial = initial := by
  apply Array.ext'
  simp

@[simp] theorem arrayAux_cons (head : α) (rest : List α) (initial : Array α) :
    (head :: rest).toArrayAux initial = rest.toArrayAux (initial.push head) := by
  apply Array.ext'
  simp [List.append_assoc]

theorem exists_trace (items : List α) (initial : Array α) :
    Trace items initial (items.toArrayAux initial) items.length := by
  induction items generalizing initial with
  | nil => simpa only [arrayAux_nil, List.length_nil] using Trace.nil initial
  | cons head rest ih =>
      simpa only [arrayAux_cons, List.length_cons] using
        Trace.cons head rest initial _ _ (ih (initial.push head))

theorem exact_trace (trace : Trace items initial result count) :
    result = items.toArrayAux initial ∧ count = items.length ∧
      result.toList = initial.toList ++ items := by
  induction trace with
  | nil initial => simp
  | cons head rest initial result count next ih =>
    refine ⟨by simpa only [arrayAux_cons] using ih.1, by simp [ih.2.1], ?_⟩
    simpa [List.append_assoc] using ih.2.2

theorem empty_array (items : List α) : Trace items #[] items.toArray items.length := by
  have same : items.toArrayAux (#[] : Array α) = items.toArray := by
    apply Array.toList_inj.mp
    simp
  rw [← same]
  exact exists_trace items (#[] : Array α)

theorem final_size (trace : Trace items initial result count) :
    result.size = initial.size + count := by
  obtain ⟨_, ticks, contents⟩ := exact_trace trace
  have length := congrArg List.length contents
  simpa [ticks] using length

end Controller.Cost.CompilerArrayTrace
