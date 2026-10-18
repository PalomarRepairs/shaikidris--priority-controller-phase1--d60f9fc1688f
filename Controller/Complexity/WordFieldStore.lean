module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.InstructionCollect

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Parsed word-list fields are consumed into an exact count-framed stack.
The destination retains an existing suffix. Unary count, delimiter and word
payload are all moved by finite instructions, including at word width zero. -/
namespace Controller.Complexity.WordFieldStore
open StackMachine StackBlocks WordReader
open scoped BigOperators

def fields (frame : Port → List Bool) (target : Port) (count payload output temporary : List Bool) : Port → List Bool :=
  Function.update (Function.update (Function.update (Function.update frame (some 12) count)
    (some 11) payload) target output) (some 20) temporary

theorem fields_at (frame : Port → List Bool) (target address : Port) (count payload output temporary : List Bool) :
    fields frame target count payload output temporary address=
      if address=some 20 then temporary else if address=target then output else if address=some 11 then payload
      else if address=some 12 then count else frame address := by
  simp only [fields, Function.update_apply]

def delimiter : Program (Fin 31) (Fin 2) where
  main := 0
  code label := if label=0 then .push (some 20) false 1 else .halt

def first := transfer (K := Fin 31) (some 12) (some 20)
def third := transfer (K := Fin 31) (some 11) (some 20)
def last (target : Port) := transfer (K := Fin 31) (some 20) target
def program (target : Port) := link (link (link first delimiter) third) (last target)

theorem count_execution (frame : Port → List Bool) (target : Port) (count : Nat) (payload output : List Bool)
    (notCount : target ≠ some 12) :
    ∃ peak, Execution first ⟨some first.main,fields frame target (List.replicate count true) payload output []⟩
      ⟨none,fields frame target [] payload output (List.replicate count true)⟩ (2*count+2) peak := by
  obtain ⟨peak,trace⟩ := InstructionCollect.move_execution (fields frame target (List.replicate count true) payload output []) (some 12) (some 20) (by decide)
  have final : Function.update (Function.update (fields frame target (List.replicate count true) payload output []) (some 12) []) (some 20)
      ((fields frame target (List.replicate count true) payload output [] (some 12)).reverse++
        fields frame target (List.replicate count true) payload output [] (some 20))=
      fields frame target [] payload output (List.replicate count true) := by
    funext address
    by_cases hc : address=some 12 <;> by_cases ht : address=some 20 <;> simp_all [fields_at, Ne.symm notCount]
  rw [final] at trace
  exact ⟨peak,by simpa [first, transfer, fields_at, Ne.symm notCount] using trace⟩

theorem delimiter_execution (frame : Port → List Bool) (target : Port) (payload output count : List Bool) :
    ∃ peak, Execution delimiter ⟨some delimiter.main,fields frame target [] payload output count⟩
      ⟨none,fields frame target [] payload output (false :: count)⟩ 2 peak := by
  have update : Function.update (fields frame target [] payload output count) (some 20)
      (false :: fields frame target [] payload output count (some 20))=fields frame target [] payload output (false :: count) := by
    funext address
    by_cases ht : address=some 20 <;> simp_all [fields_at]
  have stepOne : step delimiter ⟨some delimiter.main,fields frame target [] payload output count⟩=
      some ⟨some 1,fields frame target [] payload output (false :: count)⟩ := by simp [step, delimiter, instructionStep, update]
  have stepTwo : step delimiter ⟨some 1,fields frame target [] payload output (false :: count)⟩=
      some ⟨none,fields frame target [] payload output (false :: count)⟩ := by simp [step, delimiter, instructionStep]
  exact ⟨_,Execution.cons stepOne (Execution.cons stepTwo (Execution.refl _))⟩

theorem payload_execution (frame : Port → List Bool) (target : Port) (payload output temporary : List Bool)
    (notPayload : target ≠ some 11) :
    ∃ peak, Execution third ⟨some third.main,fields frame target [] payload output temporary⟩
      ⟨none,fields frame target [] [] output (payload.reverse++temporary)⟩ (2*payload.length+2) peak := by
  obtain ⟨peak,trace⟩ := InstructionCollect.move_execution (fields frame target [] payload output temporary) (some 11) (some 20) (by decide)
  have final : Function.update (Function.update (fields frame target [] payload output temporary) (some 11) []) (some 20)
      ((fields frame target [] payload output temporary (some 11)).reverse++fields frame target [] payload output temporary (some 20))=
      fields frame target [] [] output (payload.reverse++temporary) := by
    funext address
    by_cases hp : address=some 11 <;> by_cases ht : address=some 20 <;> simp_all [fields_at, Ne.symm notPayload]
  rw [final] at trace
  exact ⟨peak,by simpa [third, transfer, fields_at, Ne.symm notPayload] using trace⟩

theorem last_execution (frame : Port → List Bool) (target : Port) (temporary output : List Bool)
    (notTemporary : target ≠ some 20) :
    ∃ peak, Execution (last target) ⟨some (last target).main,fields frame target [] [] output temporary⟩
      ⟨none,fields frame target [] [] (temporary.reverse++output) []⟩ (2*temporary.length+2) peak := by
  obtain ⟨peak,trace⟩ := InstructionCollect.move_execution (fields frame target [] [] output temporary) (some 20) target notTemporary.symm
  have final : Function.update (Function.update (fields frame target [] [] output temporary) (some 20) []) target
      ((fields frame target [] [] output temporary (some 20)).reverse++fields frame target [] [] output temporary target)=
      fields frame target [] [] (temporary.reverse++output) [] := by
    funext address
    by_cases ht : address=some 20 <;> by_cases hd : address=target <;> simp_all [fields_at]
  rw [final] at trace
  exact ⟨peak,by simpa [last, transfer, fields_at, notTemporary] using trace⟩

theorem execution (frame : Port → List Bool) (target : Port) (words : List (Controller.Cost.Word width)) (output : List Bool)
    (notCount : target ≠ some 12) (notPayload : target ≠ some 11) (notTemporary : target ≠ some 20) :
    ∃ peak, Execution (program target)
      ⟨some (program target).main,fields frame target (List.replicate words.length true) (Encoding.wordList width words) output []⟩
      ⟨none,fields frame target [] [] (Encoding.encodeWords width words++output) []⟩ (4*(width+1)*words.length+10) peak := by
  obtain ⟨p₁,one⟩ := count_execution frame target words.length (Encoding.wordList width words) output notCount
  obtain ⟨p₂,two⟩ := delimiter_execution frame target (Encoding.wordList width words) output (List.replicate words.length true)
  obtain ⟨p₃,three⟩ := payload_execution frame target (Encoding.wordList width words) output (false :: List.replicate words.length true) notPayload
  obtain ⟨p₄,four⟩ := last_execution frame target ((Encoding.wordList width words).reverse++(false :: List.replicate words.length true)) output notTemporary
  have trace := ((one.link two).link three).link four
  have encoded : ((Encoding.wordList width words).reverse++(false :: List.replicate words.length true)).reverse++output=
      Encoding.encodeWords width words++output := by simp [Encoding.encodeWords, Encoding.frameCount, List.reverse_append, List.append_assoc]
  have ticks : ((2*words.length+2)+2+(2*(Encoding.wordList width words).length+2))+
      (2*((Encoding.wordList width words).reverse++(false :: List.replicate words.length true)).length+2)=
      4*(width+1)*words.length+10 := by simp only [Encoding.wordList_length, List.length_append, List.length_reverse, List.length_cons, List.length_replicate]; ring
  exact ⟨_,by simpa only [program, encoded, ticks] using trace⟩

theorem fields_self (frame : Port → List Bool) (target : Port) :
    fields frame target (frame (some 12)) (frame (some 11)) (frame target) (frame (some 20))=frame := by
  simp only [fields, Function.update_eq_self]

theorem ready_execution (input : Port → List Bool) (target : Port) (words : List (Controller.Cost.Word width))
    (notCount : target ≠ some 12) (notPayload : target ≠ some 11) (notTemporary : target ≠ some 20)
    (count : input (some 12)=List.replicate words.length true)
    (payload : input (some 11)=Encoding.wordList width words) (scratch : input (some 20)=[]) :
    ∃ peak, Execution (program target) ⟨some (program target).main,input⟩
      ⟨none,fields input target [] [] (Encoding.encodeWords width words++input target) []⟩
      (4*(width+1)*words.length+10) peak := by
  have entry : fields input target (List.replicate words.length true) (Encoding.wordList width words) (input target) []=input := by
    rw [← count,← payload,← scratch]
    exact fields_self input target
  simpa only [entry] using execution input target words (input target) notCount notPayload notTemporary

theorem resident (target : Port) : (∑ label, statementSize (tmStatement ((program target).code label))) ≤ 126 := by
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.reduceAdd, Nat.reduceMul] using finiteTM_resident (program target)

end Controller.Complexity.WordFieldStore
