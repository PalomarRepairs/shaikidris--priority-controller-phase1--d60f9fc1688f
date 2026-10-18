module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.OutputProgram

@[expose] public section

/-! A source compiler that retains a reversed instruction accumulator and a
cached program cursor. No step traverses the earlier instruction prefix.
Machine execution bounds and compiler construction costs are distinct. -/
namespace Controller.Cost.CompilerBuilder

open Controller.Decoder Controller.Cost.GateProgram Controller.Cost.DAGProgram

structure Builder (width : Nat) where
  cursor : Nat
  reversed : Code width

def Builder.append (builder : Builder width) (chunk : Code width) : Builder width :=
  ⟨builder.cursor + chunk.length, chunk.reverse ++ builder.reversed⟩

/-- The newly emitted chunk is the first append operand, so earlier code is shared. -/
theorem Builder.append_reversed (builder : Builder width) (chunk : Code width) :
    (builder.append chunk).reversed.reverse = builder.reversed.reverse ++ chunk := by
  simp [Builder.append, List.reverse_append]

def prefixBuilder (graph : DAG n) (width base : Nat) :
    (length : Nat) → length ≤ graph.nodeCount → Builder width
  | 0, _ => ⟨base, []⟩
  | length + 1, bound =>
      let earlier := prefixBuilder graph width base length (by omega)
      earlier.append (gateCode width earlier.cursor (graph.node ⟨length, by omega⟩))

/-- Cached cursor and code agree with the already verified program for every prefix. -/
theorem prefixBuilder_correct (graph : DAG n) (width base : Nat) :
    ∀ (length : Nat) (bound : length ≤ graph.nodeCount),
      (prefixBuilder graph width base length bound).cursor =
        base + (prefixCode graph width base length bound).length ∧
      (prefixBuilder graph width base length bound).reversed.reverse =
        prefixCode graph width base length bound := by
  intro length
  induction length with
  | zero => intro bound; simp [prefixBuilder, prefixCode]
  | succ length ih =>
    intro bound
    have earlierBound : length ≤ graph.nodeCount := by omega
    obtain ⟨cursor, code⟩ := ih earlierBound
    constructor
    · simp only [prefixBuilder, Builder.append, prefixCode, List.length_append]
      rw [cursor]; omega
    · simp only [prefixBuilder, Builder.append_reversed, prefixCode]
      rw [cursor, code]

def compile (graph : DAG n) (width : Nat) : Program width 4 :=
  let table := prefixBuilder graph width 0 graph.nodeCount (Nat.le_refl _)
  let observed := table.append
    (Controller.Cost.OutputProgram.emitCode width
      (Controller.Cost.OutputProgram.observationAddresses graph))
  (observed.reversed.reverse).toArray.push .halt

/-- The efficient source builder inherits the exact executable program, not just its size. -/
theorem compile_eq (graph : DAG n) (width : Nat) :
    compile graph width = Controller.Cost.OutputProgram.completeProgram graph width := by
  have code := (prefixBuilder_correct graph width 0 graph.nodeCount (Nat.le_refl _)).2
  simp only [compile, Builder.append_reversed, code,
    Controller.Cost.OutputProgram.completeProgram, Controller.Cost.OutputProgram.completeCode]

end Controller.Cost.CompilerBuilder
