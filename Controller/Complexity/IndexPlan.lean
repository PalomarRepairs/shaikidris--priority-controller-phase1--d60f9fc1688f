module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.IndexRange
public import Controller.Complexity.BinaryIndex

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A fixed finite program range-checks a preserved binary index before
constructing its unary traversal counter. Rejected indices leave an error
marker and an empty counter. Every work bank and ambient bank is accounted for. -/
namespace Controller.Complexity.IndexPlan
open StackMachine WordReader
open scoped BigOperators

def accept (head : Option Bool) : Bool := head.isNone

def program := GuardedLink.program IndexRange.program BinaryIndex.program none accept

def result (input : Port → List Bool) (word : List Bool) (count : Nat) : Port → List Bool :=
  Function.update (Function.update input none (if Encoding.value word<count then [] else [false]))
    (some 4) (if Encoding.value word<count then List.replicate (Encoding.value word) true else [])

theorem execution (input : Port → List Bool) (word : List Bool) (count : Nat)
    (index : input (some 3)=word) (stored : input (some 10)=List.replicate count true)
    (status : input none=[]) (wordWork : input (some 1)=[]) (bound : input (some 16)=[])
    (counter : input (some 4)=[]) (temporary : input (some 5)=[]) (working : input (some 6)=[])
    (mode : input (some 7)=[]) (scratch : input (some 17)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩
      ⟨none,result input word count⟩ ticks peak ∧
      ticks ≤ word.length*(11*count+33)+6*count+30 := by
  obtain ⟨checkTicks,checkPeak,checking,checkBound⟩ :=
    IndexRange.ready_execution input word count index stored status wordWork bound scratch
  have output (flag : List Bool) : IndexRange.bank input flag [] [] []=Function.update input none flag := by
    funext address
    by_cases hs : address=none <;> by_cases hw : address=some 1 <;>
      by_cases hb : address=some 16 <;> by_cases ht : address=some 17 <;>
      simp_all [RegisterRange.bank_at]
  rw [output] at checking
  by_cases inRange : Encoding.value word<count
  · have clean : Function.update input none ([] : List Bool)=input := by
      funext address
      by_cases same : address=none <;> simp_all
    simp only [ite_eq_left inRange,clean] at checking
    obtain ⟨convertTicks,convertPeak,converting,convertBound⟩ :=
      BinaryIndex.ready_execution input word index counter temporary working mode scratch
    have trace := GuardedLink.success none accept checking converting (by simp [accept,status])
    have final : result input word count=Function.update input (some 4) (List.replicate (Encoding.value word) true) := by
      simp only [result,ite_eq_left inRange,clean]
    rw [← final] at trace
    have product := Nat.mul_le_mul_left word.length (Nat.add_le_add_right (Nat.mul_le_mul_left 7 (Nat.le_of_lt inRange)) 23)
    have identity : word.length*(4*count+10)+6*count+17+(word.length*(7*count+23)+12)=
        word.length*(11*count+33)+6*count+29 := by ring
    exact ⟨_,_,trace,by omega⟩
  · simp only [ite_eq_right inRange] at checking
    have trace := GuardedLink.failure BinaryIndex.program none accept checking (by simp [accept])
    have final : result input word count=Function.update input none [false] := by
      simp only [result,ite_eq_right inRange]
      funext address
      by_cases same : address=some 4 <;> simp_all
    rw [← final] at trace
    have product := Nat.mul_le_mul_left word.length (show 4*count+10 ≤ 11*count+33 by omega)
    exact ⟨_,_,trace,by omega⟩

def size (input : Port → List Bool) : Nat := ∑ port : Port,(input port).length

theorem total_polynomial (input : Port → List Bool) (word : List Bool) (count : Nat)
    (index : input (some 3)=word) (stored : input (some 10)=List.replicate count true)
    (status : input none=[]) (wordWork : input (some 1)=[]) (bound : input (some 16)=[])
    (counter : input (some 4)=[]) (temporary : input (some 5)=[]) (working : input (some 6)=[])
    (mode : input (some 7)=[]) (scratch : input (some 17)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩
      ⟨none,result input word count⟩ ticks peak ∧
      ticks ≤ 11*(size input)^2+39*size input+30 ∧ peak ≤ 11*(size input)^2+40*size input+30 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution input word count index stored status wordWork bound counter temporary working mode scratch
  have cell (port : Port) : (input port).length ≤ size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have wBound : word.length ≤ size input := by simpa only [index] using cell (some 3)
  have nBound : count ≤ size input := by simpa only [stored,List.length_replicate] using cell (some 10)
  have product := Nat.mul_le_mul wBound (Nat.add_le_add_right (Nat.mul_le_mul_left 11 nBound) 33)
  have identity : size input*(11*size input+33)+6*size input+30=11*(size input)^2+39*size input+30 := by ring
  have bounded : ticks ≤ 11*(size input)^2+39*size input+30 := by rw [← identity]; omega
  have space := trace.peak_le
  change peak ≤ size input+ticks at space
  exact ⟨ticks,peak,trace,bounded,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 765 := by
  simpa only [program,IndexRange.program,IndexRange.indexMachine,IndexRange.countMachine,
    BinaryIndex.program,BinaryIndex.copyMachine,BinaryIndex.reverseMachine,StackFrames.relocate,
    StackCopy.program,StackBlocks.reverseProgram,Fintype.card_sum,Fintype.card_fin,Fintype.card_option,
    WordBound.Label,WordBound.BodyLabel,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.IndexPlan
