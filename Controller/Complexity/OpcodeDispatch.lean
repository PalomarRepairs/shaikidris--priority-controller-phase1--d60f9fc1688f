module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ControlEmbed
public import Controller.Complexity.StackEvaluation
public import Controller.Complexity.OpcodeReader

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Four actual most-significant-first opcode bits select one of sixteen
programs. The prefix and depth occupy fixed finite control; short tags enter
the supplied fallback. Body execution preserves its actual ticks and peak. -/
namespace Controller.Complexity.OpcodeDispatch
open StackMachine WordReader
open scoped BigOperators

def Label (labels : Fin 16 → Type) : Type := (Fin 4 × Fin 16) ⊕ (Σ tag, labels tag)
def size (input : Port → List Bool) : Nat := ∑ port : Port,(input port).length
def enter {labels : Fin 16 → Type} (tag : Fin 16) (label : labels tag) : Label labels := .inr ⟨tag,label⟩
def digit (value : Fin 16) (bit : Bool) : Fin 16 := ⟨(2*value.val+(if bit then 1 else 0))%16,Nat.mod_lt _ (by decide)⟩

def advance {labels : Fin 16 → Type} (family : ∀ tag, Program (Fin 31) (labels tag))
    (depth : Fin 4) (value : Fin 16) (bit : Bool) : Label labels :=
  let next := digit value bit
  if depth.val=3 then enter next (family next).main else .inl (⟨(depth.val+1)%4,Nat.mod_lt _ (by decide)⟩,next)

def program {labels : Fin 16 → Type} (family : ∀ tag, Program (Fin 31) (labels tag)) (fallback : Fin 16) : Program (Fin 31) (Label labels) where
  main := .inl (0,0)
  code label := match label with
    | .inl (depth,value) => .pop (some 13) (enter fallback (family fallback).main)
        (advance family depth value false) (advance family depth value true)
    | .inr ⟨tag,label⟩ => ControlEmbed.instruction (enter tag) ((family tag).code label)

theorem body_execution {labels : Fin 16 → Type} (family : ∀ tag, Program (Fin 31) (labels tag)) (fallback tag : Fin 16)
    {input output : Port → List Bool} {ticks peak}
    (trace : Execution (family tag) ⟨some (family tag).main,input⟩ ⟨none,output⟩ ticks peak) :
    Execution (program family fallback) ⟨some (enter tag (family tag).main),input⟩ ⟨none,output⟩ ticks peak :=
  ControlEmbed.execution (family tag) (program family fallback) (enter tag) (fun _ => rfl) trace

theorem pop_step {labels : Fin 16 → Type} (family : ∀ tag, Program (Fin 31) (labels tag)) (fallback : Fin 16)
    (depth : Fin 4) (value : Fin 16) (input : Port → List Bool) (bit : Bool) (rest : List Bool) :
    StackMachine.step (program family fallback) ⟨some (.inl (depth,value)),Function.update input (some 13) (bit :: rest)⟩=
      some ⟨some (advance family depth value bit),Function.update input (some 13) rest⟩ := by
  change some (instructionStep (.pop (some 13) (enter fallback (family fallback).main)
    (advance family depth value false) (advance family depth value true))
    (⟨some (.inl (depth,value)),Function.update input (some 13) (bit :: rest)⟩ : State (Fin 31) (Label labels)))=_
  cases bit <;> simp [instructionStep]

theorem four_steps {labels : Fin 16 → Type} (family : ∀ tag, Program (Fin 31) (labels tag)) (fallback : Fin 16)
    (input : Port → List Bool) (a b c d : Bool) :
    ∃ peak, Execution (program family fallback)
      ⟨some (program family fallback).main,Function.update input (some 13) [a,b,c,d]⟩
      ⟨some (enter (digit (digit (digit (digit 0 a) b) c) d) (family (digit (digit (digit (digit 0 a) b) c) d)).main),Function.update input (some 13) []⟩ 4 peak := by
  have first := pop_step family fallback 0 0 input a [b,c,d]
  have second := pop_step family fallback 1 (digit 0 a) input b [c,d]
  have third := pop_step family fallback 2 (digit (digit 0 a) b) input c [d]
  have fourth := pop_step family fallback 3 (digit (digit (digit 0 a) b) c) input d []
  exact ⟨_,Execution.cons first (Execution.cons second (Execution.cons third (Execution.cons fourth (Execution.refl _))))⟩

theorem selected_execution {labels : Fin 16 → Type} (family : ∀ tag, Program (Fin 31) (labels tag)) (fallback tag : Fin 16) (input : Port → List Bool) :
    ∃ peak, Execution (program family fallback)
      ⟨some (program family fallback).main,Function.update input (some 13) (Encoding.bits 4 tag.val).reverse⟩
      ⟨some (enter tag (family tag).main),Function.update input (some 13) []⟩ 4 peak := by
  fin_cases tag
  · simpa [Encoding.bits,digit] using four_steps family fallback input false false false false
  · simpa [Encoding.bits,digit] using four_steps family fallback input false false false true
  · simpa [Encoding.bits,digit] using four_steps family fallback input false false true false
  · simpa [Encoding.bits,digit] using four_steps family fallback input false false true true
  · simpa [Encoding.bits,digit] using four_steps family fallback input false true false false
  · simpa [Encoding.bits,digit] using four_steps family fallback input false true false true
  · simpa [Encoding.bits,digit] using four_steps family fallback input false true true false
  · simpa [Encoding.bits,digit] using four_steps family fallback input false true true true
  · simpa [Encoding.bits,digit] using four_steps family fallback input true false false false
  · simpa [Encoding.bits,digit] using four_steps family fallback input true false false true
  · simpa [Encoding.bits,digit] using four_steps family fallback input true false true false
  · simpa [Encoding.bits,digit] using four_steps family fallback input true false true true
  · simpa [Encoding.bits,digit] using four_steps family fallback input true true false false
  · simpa [Encoding.bits,digit] using four_steps family fallback input true true false true
  · simpa [Encoding.bits,digit] using four_steps family fallback input true true true false
  · simpa [Encoding.bits,digit] using four_steps family fallback input true true true true

theorem selection {labels : Fin 16 → Type} (family : ∀ tag, Program (Fin 31) (labels tag)) (fallback tag : Fin 16)
    (input : Port → List Bool) (stored : input (some 13)=(Encoding.bits 4 tag.val).reverse) :
    ∃ peak, Execution (program family fallback) ⟨some (program family fallback).main,input⟩
      ⟨some (enter tag (family tag).main),Function.update input (some 13) []⟩ 4 peak := by
  obtain ⟨peak,trace⟩ := selected_execution family fallback tag input
  have original : Function.update input (some 13) (Encoding.bits 4 tag.val).reverse=input := by rw [← stored,Function.update_eq_self]
  rw [original] at trace
  exact ⟨_,trace⟩

theorem execution {labels : Fin 16 → Type} (family : ∀ tag, Program (Fin 31) (labels tag)) (fallback tag : Fin 16)
    (input output : Port → List Bool) (stored : input (some 13)=(Encoding.bits 4 tag.val).reverse) {ticks peak}
    (trace : Execution (family tag) ⟨some (family tag).main,Function.update input (some 13) []⟩ ⟨none,output⟩ ticks peak) :
    ∃ totalPeak, Execution (program family fallback) ⟨some (program family fallback).main,input⟩ ⟨none,output⟩ (4+ticks) totalPeak ∧
      totalPeak ≤ size input+(4+ticks) := by
  obtain ⟨selectPeak,selecting⟩ := selection family fallback tag input stored
  have body := body_execution family fallback tag trace
  have joined := selecting.append body
  exact ⟨_,joined,joined.peak_le⟩

end Controller.Complexity.OpcodeDispatch
