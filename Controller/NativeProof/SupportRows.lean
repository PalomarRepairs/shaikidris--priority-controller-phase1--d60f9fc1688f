module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.NativeProof.SourceHealthyOneQuery
public import Controller.NativeProof.DecoderSupport
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-! Native support-summary elimination preserves stronger clauses and skips
leaf identities. Heads use sorted finite supports; summary rows are reused at
each stored incidence rather than expanded into a proof tree. -/
namespace Controller.NativeProof.SupportRows
open Controller.CNF Controller.Resolution
open Controller.NativeProof.FoldProjection Controller.NativeProof.SourceStageCongruence
variable {v : Nat}

inductive Summary (state : State v) (context : Clause (Fin v))
    (output : Literal (Fin v)) (heads : Clause (Fin v)) : Type
  | identity (same : heads = [output])
  | derived (row : AvailableSubclause state (context ++ negate output :: heads))

def Summary.afterTrace (summary : Summary state context output heads)
    (next : State v) (steps : List (Step v)) (checked : runSteps state steps = some next) :
    Summary next context output heads :=
  match summary with
  | .identity same => .identity same
  | .derived row => .derived (FoldProjection.afterTrace row next steps checked)

def Summary.emptyRow (summary : Summary state context output []) :
    AvailableSubclause state (context ++ [negate output]) :=
  match summary with
  | .identity same => False.elim (by have length := congrArg List.length same; simp at length)
  | .derived row => row

def expand (state : State v) (context target : Clause (Fin v)) (output : Literal (Fin v))
    (heads : Clause (Fin v)) (summary : Summary state context output heads)
    (parent : AvailableSubclause state (output :: target))
    (contextIncluded : ClauseSubset context target) (headsIncluded : ClauseSubset heads target) :
    SubclauseProjection state target 1 := by
  cases summary with
  | identity same =>
    have included : output ∈ target := headsIncluded output (by rw [same]; simp)
    exact ⟨state, [], rfl, retarget parent (fun literal member => (List.mem_cons.mp member).elim
      (fun equal => equal ▸ included) id), by simp⟩
  | derived row =>
    let negative : AvailableSubclause state (negate output :: target) := retarget row (by
      intro literal member
      rcases List.mem_append.mp member with old | other
      · exact List.mem_cons_of_mem _ (contextIncluded literal old)
      · rcases List.mem_cons.mp other with pivot | head
        · exact List.mem_cons.mpr (Or.inl pivot)
        · exact List.mem_cons_of_mem _ (headsIncluded literal head))
    let joined := longMerge state output target target negative parent
    exact ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _,
      retarget (longMerge_result _ _ _ _ _ _) (by
        intro literal member
        exact (List.mem_append.mp member).elim id id), longMerge_count _ _ _ _ _ _⟩

def heads (support : Finset (Fin n)) (handle : Fin n → Literal (Fin v)) : Clause (Fin v) :=
  (support.sort (· ≤ ·)).map handle

@[simp] theorem heads_empty (handle : Fin n → Literal (Fin v)) : heads ∅ handle = [] := by simp [heads]
@[simp] theorem heads_singleton (channel : Fin n) (handle : Fin n → Literal (Fin v)) :
    heads {channel} handle = [handle channel] := by simp [heads]

theorem heads_member (support : Finset (Fin n)) (handle : Fin n → Literal (Fin v))
    (literal : Literal (Fin v)) : literal ∈ heads support handle ↔ ∃ channel ∈ support, handle channel = literal := by
  simp [heads]

def erase (state : State v) (context : Clause (Fin v)) (output : Literal (Fin v))
    (support : Finset (Fin n)) (handle : Fin n → Literal (Fin v)) (channel : Fin n)
    (parent : AvailableSubclause state (context ++ negate output :: heads support handle))
    (blocked : AvailableSubclause state [negate output, negate (handle channel)]) :
    SubclauseProjection state (context ++ negate output :: heads (support.erase channel) handle) 1 := by
  let target := context ++ negate output :: heads (support.erase channel) handle
  let positive : AvailableSubclause state (handle channel :: target) := retarget parent (by
    intro literal member
    rcases List.mem_append.mp member with old | rest
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ old)
    · rcases List.mem_cons.mp rest with root | head
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons.mpr (Or.inl root)))
      · obtain ⟨source, present, same⟩ := (heads_member support handle literal).mp head
        by_cases equal : source = channel
        · exact List.mem_cons.mpr (Or.inl (same.symm.trans (congrArg handle equal)))
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _
            ((heads_member (support.erase channel) handle literal).mpr ⟨source, Finset.mem_erase.mpr ⟨equal, present⟩, same⟩))))
  let negative : AvailableSubclause state (negate (handle channel) :: target) := retarget blocked (by
    intro literal member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with root | head
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons.mpr (Or.inl root)))
    · exact List.mem_cons.mpr (Or.inl head))
  let joined := longMerge state (handle channel) target target negative positive
  exact ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _,
    retarget (longMerge_result _ _ _ _ _ _) (fun literal member => (List.mem_append.mp member).elim id id),
    longMerge_count _ _ _ _ _ _⟩

def kill (state : State v) (context : Clause (Fin v)) (output head : Literal (Fin v))
    (blocked : AvailableSubclause state [negate output, negate head])
    (unit : AvailableSubclause state (context ++ [head])) :
    SubclauseProjection state (context ++ [negate output]) 1 := by
  let negative : AvailableSubclause state (negate head :: [negate output]) := retarget blocked (by
    intro literal member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop)
  let positive : AvailableSubclause state (head :: context) := retarget unit (by
    intro literal member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    aesop)
  let joined := longMerge state head [negate output] context negative positive
  exact ⟨joined.state, joined.steps, longMerge_run _ _ _ _ _ _,
    retarget (longMerge_result _ _ _ _ _ _) (by
      intro literal member
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      aesop), longMerge_count _ _ _ _ _ _⟩

/-- Assemble one checked support elimination outside its recursive equations. -/
def eliminateStep {α : Type} (state : State v) (context target : Clause (Fin v))
    (item : α) (rest : List α) (label : α → Literal (Fin v)) (supportHeads : α → Clause (Fin v))
    (summaries : ∀ query ∈ item :: rest, Summary state context (label query) (supportHeads query))
    (contextIncluded : ClauseSubset context target)
    (headsIncluded : ∀ query ∈ item :: rest, ClauseSubset (supportHeads query) target)
    (parent : AvailableSubclause state ((item :: rest).map label ++ target))
    (recurse : ∀ (next : State v),
      (∀ old ∈ rest, Summary next context (label old) (supportHeads old)) →
      AvailableSubclause next (rest.map label ++ target) →
      SubclauseProjection next target rest.length) :
    SubclauseProjection state target (item :: rest).length := by
  let expanded := expand state context (rest.map label ++ target) (label item) (supportHeads item)
    (summaries item List.mem_cons_self) parent
    (fun literal member => List.mem_append_right _ (contextIncluded literal member))
    (fun literal member => List.mem_append_right _ (headsIncluded item List.mem_cons_self literal member))
  let tail := recurse expanded.state
    (fun old present => (summaries old (List.mem_cons_of_mem _ present)).afterTrace expanded.state expanded.steps expanded.checked)
    expanded.result
  refine ⟨tail.state, expanded.steps ++ tail.steps, ?_, tail.result, ?_⟩
  · rw [runSteps_append, expanded.checked]
    exact tail.checked
  · have first := expanded.count
    have second := tail.count
    simp only [List.length_append, List.length_cons]
    omega


def eliminate {α : Type} (state : State v) (context target : Clause (Fin v))
    (items : List α) (label : α → Literal (Fin v)) (supportHeads : α → Clause (Fin v))
    (summaries : ∀ item ∈ items, Summary state context (label item) (supportHeads item))
    (contextIncluded : ClauseSubset context target)
    (headsIncluded : ∀ item ∈ items, ClauseSubset (supportHeads item) target)
    (parent : AvailableSubclause state (items.map label ++ target)) :
    SubclauseProjection state target items.length :=
  match items with
  | [] => ⟨state, [], rfl, parent, by simp⟩
  | item :: rest =>
    eliminateStep state context target item rest label supportHeads summaries
      contextIncluded headsIncluded parent
      (fun next restSummaries nextParent =>
        eliminate next context target rest label supportHeads restSummaries contextIncluded
          (fun old present => headsIncluded old (List.mem_cons_of_mem _ present)) nextParent)

structure Erased (state : State v) (context : Clause (Fin v)) (output : Literal (Fin v))
    (support : Finset (Fin n)) (handle : Fin n → Literal (Fin v)) (labels : List (Fin n)) where
  next : State v
  steps : List (Step v)
  checked : runSteps state steps = some next
  result : AvailableSubclause next (context ++ negate output :: heads (support \ labels.toFinset) handle)
  count : steps.length ≤ labels.length

/-- Assemble one checked support erasure outside its recursive equations. -/
def eraseLabelsStep (state : State v) (context : Clause (Fin v)) (output : Literal (Fin v))
    (support : Finset (Fin n)) (handle : Fin n → Literal (Fin v)) (channel : Fin n) (rest : List (Fin n))
    (parent : AvailableSubclause state (context ++ negate output :: heads support handle))
    (blocked : ∀ query ∈ channel :: rest, AvailableSubclause state [negate output, negate (handle query)])
    (recurse : ∀ (next : State v),
      AvailableSubclause next (context ++ negate output :: heads (support.erase channel) handle) →
      (∀ old ∈ rest, AvailableSubclause next [negate output, negate (handle old)]) →
      Erased next context output (support.erase channel) handle rest) :
    Erased state context output support handle (channel :: rest) := by
  let removed := erase state context output support handle channel parent (blocked channel List.mem_cons_self)
  let tail := recurse removed.state removed.result
    (fun old present => FoldProjection.afterTrace (blocked old (List.mem_cons_of_mem _ present)) removed.state removed.steps removed.checked)
  have sets : support.erase channel \ rest.toFinset = support \ (channel :: rest).toFinset := by
    ext head
    simp [Finset.mem_erase, Finset.mem_sdiff, and_assoc, and_left_comm, and_comm]
  refine ⟨tail.next, removed.steps ++ tail.steps, ?_, ?_, ?_⟩
  · rw [runSteps_append, removed.checked]
    exact tail.checked
  · simpa only [sets] using tail.result
  · have first := removed.count
    have second := tail.count
    simp only [List.length_append, List.length_cons]
    omega


def eraseLabels (state : State v) (context : Clause (Fin v)) (output : Literal (Fin v))
    (support : Finset (Fin n)) (handle : Fin n → Literal (Fin v)) (labels : List (Fin n))
    (parent : AvailableSubclause state (context ++ negate output :: heads support handle))
    (blocked : ∀ channel ∈ labels, AvailableSubclause state [negate output, negate (handle channel)]) :
    Erased state context output support handle labels :=
  match labels with
  | [] => ⟨state, [], rfl, by simpa using parent, by simp⟩
  | channel :: rest =>
    eraseLabelsStep state context output support handle channel rest parent blocked
      (fun next nextParent nextBlocked =>
        eraseLabels next context output (support.erase channel) handle rest nextParent nextBlocked)

end Controller.NativeProof.SupportRows
