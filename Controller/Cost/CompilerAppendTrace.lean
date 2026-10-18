module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.CompilerBuilder

@[expose] public section

/-! Concrete list traversals refining a builder update. The trace counts visited
list cells in length, accumulator reversal, and prefix copying. Existing code
is the second append operand and is never traversed. Gate-code generation,
final array conversion and a RAM compiler implementation are separate. -/
namespace Controller.Cost.CompilerAppendTrace
open Controller.Cost.GateProgram Controller.Cost.CompilerBuilder

inductive ReverseTrace {α : Type} : List α → List α → List α → Nat → Prop
  | nil (tail : List α) : ReverseTrace [] tail tail 0
  | cons (head : α) (rest tail result : List α) (count : Nat)
      (next : ReverseTrace rest (head :: tail) result count) :
      ReverseTrace (head :: rest) tail result (count + 1)

inductive AppendTrace {α : Type} : List α → List α → List α → Nat → Prop
  | nil (tail : List α) : AppendTrace [] tail tail 0
  | cons (head : α) (rest tail result : List α) (count : Nat)
      (next : AppendTrace rest tail result count) :
      AppendTrace (head :: rest) tail (head :: result) (count + 1)

inductive LengthTrace {α : Type} : List α → Nat → Nat → Prop
  | nil : LengthTrace [] 0 0
  | cons (head : α) (rest : List α) (length count : Nat)
      (next : LengthTrace rest length count) :
      LengthTrace (head :: rest) (length + 1) (count + 1)

theorem reverse_exists (items tail : List α) :
    ReverseTrace items tail (items.reverse ++ tail) items.length := by
  induction items generalizing tail with
  | nil => simpa using ReverseTrace.nil tail
  | cons head rest ih =>
    simpa [List.reverse_cons, List.append_assoc] using
      ReverseTrace.cons head rest tail (rest.reverse ++ head :: tail) rest.length (ih (head :: tail))

theorem reverse_exact (trace : ReverseTrace items tail result count) :
    result = items.reverse ++ tail ∧ count = items.length := by
  induction trace with
  | nil tail => simp
  | cons head rest tail result count next ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]
    obtain ⟨value, cost⟩ := ih
    exact ⟨value, by omega⟩

theorem append_exists (items tail : List α) :
    AppendTrace items tail (items ++ tail) items.length := by
  induction items with
  | nil => exact AppendTrace.nil tail
  | cons head rest ih => exact AppendTrace.cons head rest tail (rest ++ tail) rest.length ih

theorem append_exact (trace : AppendTrace items tail result count) :
    result = items ++ tail ∧ count = items.length := by
  induction trace with
  | nil tail => simp
  | cons head rest tail result count next ih =>
    obtain ⟨value, cost⟩ := ih
    simp [value, cost]

theorem length_exists (items : List α) : LengthTrace items items.length items.length := by
  induction items with
  | nil => exact LengthTrace.nil
  | cons head rest ih => exact LengthTrace.cons head rest rest.length rest.length ih

theorem length_exact (trace : LengthTrace items length count) :
    length = items.length ∧ count = items.length := by
  induction trace with
  | nil => simp
  | cons head rest length count next ih =>
    obtain ⟨value, cost⟩ := ih
    simp [value, cost]

/-- These are three actual recursive traversals; the output cursor update is one
additional arithmetic operation. The prior instruction list is only a tail. -/
def BuilderTrace (before : Builder width) (chunk : Code width)
    (after : Builder width) (visits : Nat) : Prop :=
  ∃ chunkLength reversedChunk copiedChunk lengthVisits reverseVisits appendVisits,
    LengthTrace chunk chunkLength lengthVisits ∧
    ReverseTrace chunk [] reversedChunk reverseVisits ∧
    AppendTrace reversedChunk before.reversed copiedChunk appendVisits ∧
    after.cursor = before.cursor + chunkLength ∧
    after.reversed = copiedChunk ∧
    visits = lengthVisits + reverseVisits + appendVisits + 1

theorem builder_exists (before : Builder width) (chunk : Code width) :
    BuilderTrace before chunk (before.append chunk) (3 * chunk.length + 1) := by
  refine ⟨chunk.length, chunk.reverse, chunk.reverse ++ before.reversed,
    chunk.length, chunk.length, chunk.length, length_exists chunk, ?_, ?_, rfl, rfl, by omega⟩
  · simpa using reverse_exists chunk []
  · simpa using append_exists chunk.reverse before.reversed

theorem builder_exact (trace : BuilderTrace before chunk after visits) :
    after = before.append chunk ∧ visits = 3 * chunk.length + 1 := by
  obtain ⟨chunkLength, reversedChunk, copiedChunk, lengthVisits, reverseVisits,
    appendVisits, lengthTrace, reverseTrace, appendTrace, finalCursor, finalCode, total⟩ := trace
  obtain ⟨len, lenCost⟩ := length_exact lengthTrace
  obtain ⟨rev, revCost⟩ := reverse_exact reverseTrace
  obtain ⟨copied, appendCost⟩ := append_exact appendTrace
  have revEq : reversedChunk = chunk.reverse := by simpa using rev
  have appendCost' : appendVisits = chunk.length := by simpa [revEq] using appendCost
  constructor
  · cases after with
    | mk cursor reversed =>
      simp only [Builder.append, Builder.mk.injEq]
      exact ⟨by simpa [len] using finalCursor, by simpa [revEq] using finalCode.trans copied⟩
  · rw [total, lenCost, revCost, appendCost']; omega

/-- The cost is independent of the length of previously accumulated code. -/
theorem prior_prefix_independent (left right : Builder width) (chunk : Code width) :
    ∃ leftAfter rightAfter,
      BuilderTrace left chunk leftAfter (3 * chunk.length + 1) ∧
      BuilderTrace right chunk rightAfter (3 * chunk.length + 1) :=
  ⟨left.append chunk, right.append chunk, builder_exists left chunk, builder_exists right chunk⟩
open Controller.Decoder Controller.Cost.DAGProgram

/-- A source construction trace records the actual prefix recursion and builder
updates. It does not charge gate-chunk generation or final array conversion. -/
def PrefixTrace (graph : DAG n) (width base : Nat) :
    (length : Nat) → length ≤ graph.nodeCount → Nat → Prop
  | 0, _, visits => visits = 0
  | length + 1, bound, visits =>
    let earlier := prefixBuilder graph width base length (by omega)
    let chunk := gateCode width earlier.cursor (graph.node ⟨length, by omega⟩)
    ∃ earlierVisits chunkVisits,
      PrefixTrace graph width base length (by omega) earlierVisits ∧
      BuilderTrace earlier chunk (earlier.append chunk) chunkVisits ∧
      visits = earlierVisits + chunkVisits

theorem prefix_exists (graph : DAG n) (width base : Nat) :
    ∀ length (bound : length ≤ graph.nodeCount),
      PrefixTrace graph width base length bound
        (3 * (prefixCode graph width base length bound).length + length) := by
  intro length
  induction length with
  | zero => intro bound; rfl
  | succ length ih =>
    intro bound
    have earlierBound : length ≤ graph.nodeCount := by omega
    let earlier := prefixBuilder graph width base length earlierBound
    let chunk := gateCode width earlier.cursor (graph.node ⟨length, by omega⟩)
    refine ⟨3 * (prefixCode graph width base length earlierBound).length + length,
      3 * chunk.length + 1, ih earlierBound, builder_exists earlier chunk, ?_⟩
    have cursor := (prefixBuilder_correct graph width base length earlierBound).1
    simp only [prefixCode, List.length_append]
    have chunkEq : chunk = gateCode width
        (base + (prefixCode graph width base length earlierBound).length)
        (graph.node ⟨length, by omega⟩) := by
      simp only [chunk, earlier, cursor]
    rw [chunkEq]
    omega

/-- Three source list traversals per emitted instruction and one cursor update
per node suffice, including repeated guard/child occurrences. -/
theorem full_prefix_linear (graph : DAG n) (width base : Nat) :
    ∃ visits, PrefixTrace graph width base graph.nodeCount (Nat.le_refl _) visits ∧
      visits ≤ 37 * graph.countedSize := by
  refine ⟨3 * (prefixCode graph width base graph.nodeCount (Nat.le_refl _)).length +
    graph.nodeCount, prefix_exists graph width base graph.nodeCount (Nat.le_refl _), ?_⟩
  have codeBound := fullCode_length_le graph width base
  have nodeBound : graph.nodeCount ≤ graph.countedSize := by rw [DAG.countedSize_eq]; omega
  omega
end Controller.Cost.CompilerAppendTrace
