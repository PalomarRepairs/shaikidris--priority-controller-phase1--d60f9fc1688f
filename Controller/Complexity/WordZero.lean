module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.LoadBody

@[expose] public section

/-! A four-label scan consumes a binary word and publishes empty status
exactly for zero. A nonzero word publishes [false]; both cases clear the
word bank and preserve every other bank. -/
namespace Controller.Complexity.WordZero
open StackMachine WordReader
open scoped BigOperators

def program : Program (Fin 31) (Fin 4) where
  main := 0
  code label := if label=0 then .pop (some 27) 3 0 1
    else if label=1 then .push none false 2
    else if label=2 then .pop (some 27) 3 2 2 else .halt

def output (input : Port → List Bool) (word : List Bool) :=
  Function.update (Function.update input (some 27) []) none (if Encoding.value word=0 then [] else [false])

theorem clear_execution (input : Port → List Bool) (word : List Bool) :
    ∃ peak, Execution program ⟨some 2,Function.update input (some 27) word⟩
      ⟨none,Function.update input (some 27) []⟩ (word.length+2) peak := by
  induction word with
  | nil =>
    have first : step program ⟨some 2,Function.update input (some 27) []⟩=some ⟨some 3,Function.update input (some 27) []⟩ := by simp [step,program,instructionStep]
    have last : step program ⟨some 3,Function.update input (some 27) []⟩=some ⟨none,Function.update input (some 27) []⟩ := rfl
    exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩
  | cons bit word ih =>
    obtain ⟨peak,tail⟩ := ih
    have first : step program ⟨some 2,Function.update input (some 27) (bit :: word)⟩=some ⟨some 2,Function.update input (some 27) word⟩ := by cases bit <;> simp [step,program,instructionStep]
    exact ⟨_,by simpa only [List.length_cons,Nat.add_right_comm] using Execution.cons first tail⟩

theorem execution (input : Port → List Bool) (word : List Bool) (clean : input none=[]) :
    ∃ peak, Execution program ⟨some program.main,Function.update input (some 27) word⟩
      ⟨none,output input word⟩ (word.length+(if Encoding.value word=0 then 2 else 3)) peak := by
  induction word with
  | nil =>
    have first : step program ⟨some program.main,Function.update input (some 27) []⟩=some ⟨some 3,Function.update input (some 27) []⟩ := by simp [step,program,instructionStep]
    have last : step program ⟨some 3,Function.update input (some 27) []⟩=some ⟨none,Function.update input (some 27) []⟩ := rfl
    have final : Function.update input (some 27) []=output input [] := by
      funext port
      by_cases hn : port=none <;> simp_all [output,Encoding.value]
    exact ⟨_,by simpa only [List.length_nil,Encoding.value,↓reduceIte,Nat.zero_add,Nat.reduceAdd,final] using Execution.cons first (Execution.cons last (Execution.refl _))⟩
  | cons bit word ih =>
    cases bit with
    | false =>
      obtain ⟨peak,tail⟩ := ih
      have first : step program ⟨some program.main,Function.update input (some 27) (false :: word)⟩=some ⟨some program.main,Function.update input (some 27) word⟩ := by simp [step,program,instructionStep]
      exact ⟨_,by simpa [output,Encoding.value,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using Execution.cons first tail⟩
    | true =>
      let marked := Function.update input none [false]
      obtain ⟨peak,tail⟩ := clear_execution marked word
      have first : step program ⟨some program.main,Function.update input (some 27) (true :: word)⟩=some ⟨some 1,Function.update input (some 27) word⟩ := by simp [step,program,instructionStep]
      have commute : Function.update (Function.update input (some 27) word) none [false]=Function.update marked (some 27) word := by
        funext port
        by_cases hn : port=none <;> by_cases hv : port=some 27 <;> simp_all [marked]
      have second : step program ⟨some 1,Function.update input (some 27) word⟩=some ⟨some 2,Function.update marked (some 27) word⟩ := by
        simpa [step,program,instructionStep,clean] using congrArg (fun bank => some (⟨some 2,bank⟩ : State (Fin 31) (Fin 4))) commute
      have final : Function.update marked (some 27) []=output input (true :: word) := by
        funext port
        by_cases hn : port=none <;> by_cases hv : port=some 27 <;> simp_all [marked,output,Encoding.value]
      exact ⟨_,by simpa [List.length_cons,Encoding.value,final,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Execution.cons first (Execution.cons second tail)⟩

theorem encoded_execution (input : Port → List Bool) (value : Controller.Cost.Word width)
    (stored : input (some 27)=Encoding.bits width value.val) (clean : input none=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩
      ⟨none,Function.update (Function.update input (some 27) []) none (if value.val=0 then [] else [false])⟩ ticks peak ∧
      ticks ≤ width+3 ∧ peak ≤ FetchSetup.size input+width+3 := by
  obtain ⟨peak,trace⟩ := execution input (Encoding.bits width value.val) clean
  have original : Function.update input (some 27) (Encoding.bits width value.val)=input := by rw [← stored,Function.update_eq_self]
  rw [original] at trace
  simp only [output,Encoding.bits_length,Encoding.value_bits width value.val value.isLt] at trace
  have timeBound : width+(if value.val=0 then 2 else 3) ≤ width+3 := by split <;> omega
  have space := trace.peak_le
  exact ⟨_,peak,trace,timeBound,by change peak ≤ FetchSetup.size input+_ at space; omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 36 := by
  simpa only [Fintype.card_fin,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.WordZero
