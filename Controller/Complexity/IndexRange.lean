module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.RegisterRange

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A preserved binary index in bank3 is compared with a preserved unary
list count in bank10. Only copied operands reach the halving comparator;
result publication and workspace cleanup are executed. -/
namespace Controller.Complexity.IndexRange
open StackMachine WordReader
open scoped BigOperators
abbrev bank := RegisterRange.bank

def indexPorts : Option Bool ↪ Port := StackFrames.threePorts (some 3) (some 1) (some 17) (by decide) (by decide) (by decide)
def countPorts : Option Bool ↪ Port := StackFrames.threePorts (some 10) (some 16) (some 17) (by decide) (by decide) (by decide)

theorem indexPorts_apply (port : Option Bool) : indexPorts port=(match port with | none => some 3 | some false => some 1 | some true => some 17) := rfl
theorem countPorts_apply (port : Option Bool) : countPorts port=(match port with | none => some 10 | some false => some 16 | some true => some 17) := rfl

def indexMachine := StackFrames.relocate indexPorts StackCopy.program
def countMachine := StackFrames.relocate countPorts StackCopy.program
def program := link (link (link indexMachine countMachine) RegisterRange.coreMachine) RegisterRange.publishMachine

theorem index_execution (frame : Port → List Bool) (word : List Bool) (stored : frame (some 3)=word) :
    ∃ peak, Execution indexMachine ⟨some indexMachine.main,bank frame [] [] [] []⟩
      ⟨none,bank frame [] word [] []⟩ (5*word.length+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution indexPorts (bank frame [] [] [] []) (by simp [indexPorts_apply,RegisterRange.bank_at])
  have output : Function.update (bank frame [] [] [] []) (indexPorts (some false))
      (bank frame [] [] [] [] (indexPorts none)++bank frame [] [] [] [] (indexPorts (some false)))=bank frame [] word [] [] := by
    funext address
    by_cases same : address=some 1 <;> simp_all [indexPorts_apply,RegisterRange.bank_at]
  rw [output] at trace
  exact ⟨peak,by simpa [indexMachine,StackFrames.relocate,indexPorts_apply,RegisterRange.bank_at,stored] using trace⟩

theorem count_execution (frame : Port → List Bool) (word : List Bool) (count : Nat) (stored : frame (some 10)=List.replicate count true) :
    ∃ peak, Execution countMachine ⟨some countMachine.main,bank frame [] word [] []⟩
      ⟨none,bank frame [] word (List.replicate count true) []⟩ (5*count+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution countPorts (bank frame [] word [] []) (by simp [countPorts_apply,RegisterRange.bank_at])
  have output : Function.update (bank frame [] word [] []) (countPorts (some false))
      (bank frame [] word [] [] (countPorts none)++bank frame [] word [] [] (countPorts (some false)))=
      bank frame [] word (List.replicate count true) [] := by
    funext address
    by_cases same : address=some 16 <;> simp_all [countPorts_apply,RegisterRange.bank_at]
  rw [output] at trace
  exact ⟨peak,by simpa [countMachine,StackFrames.relocate,countPorts_apply,RegisterRange.bank_at,stored] using trace⟩

theorem execution (frame : Port → List Bool) (word : List Bool) (count : Nat)
    (index : frame (some 3)=word) (stored : frame (some 10)=List.replicate count true) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] [] [] []⟩
      ⟨none,bank frame (if Encoding.value word<count then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ word.length*(4*count+10)+6*count+17 := by
  obtain ⟨indexPeak,copyIndex⟩ := index_execution frame word index
  obtain ⟨countPeak,copyCount⟩ := count_execution frame word count stored
  obtain ⟨coreTicks,corePeak,checking,coreBound⟩ := RegisterRange.core_execution frame word count
  obtain ⟨flagTicks,flagPeak,publishing,flagBound⟩ := RegisterRange.publish_execution frame (Encoding.value word<count)
  have trace := ((copyIndex.link copyCount).link checking).link publishing
  have identity : (5*word.length+4)+(5*count+4)+(word.length*(4*count+5)+count+5)+4=
      word.length*(4*count+10)+6*count+17 := by ring
  exact ⟨_,_,trace,by omega⟩

theorem ready_execution (input : Port → List Bool) (word : List Bool) (count : Nat)
    (index : input (some 3)=word) (stored : input (some 10)=List.replicate count true)
    (status : input none=[]) (result : input (some 1)=[]) (bound : input (some 16)=[]) (scratch : input (some 17)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩
      ⟨none,bank input (if Encoding.value word<count then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ word.length*(4*count+10)+6*count+17 := by
  have entry : bank input [] [] [] []=input := by
    funext address
    by_cases hs : address=none <;> by_cases hw : address=some 1 <;> by_cases hb : address=some 16 <;> by_cases ht : address=some 17 <;>
      simp_all [RegisterRange.bank_at]
  simpa only [entry] using execution input word count index stored

def size (frame : Port → List Bool) := ∑ port : Port,(bank frame [] [] [] [] port).length

theorem total_polynomial (frame : Port → List Bool) (word : List Bool) (count : Nat)
    (index : frame (some 3)=word) (stored : frame (some 10)=List.replicate count true) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] [] [] []⟩
      ⟨none,bank frame (if Encoding.value word<count then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ 4*(size frame)^2+16*size frame+17 ∧ peak ≤ 4*(size frame)^2+17*size frame+17 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution frame word count index stored
  have cell (port : Port) : (bank frame [] [] [] [] port).length ≤ size frame :=
    Finset.single_le_sum (f := fun address : Port => (bank frame [] [] [] [] address).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have wBound : word.length ≤ size frame := by simpa [RegisterRange.bank_at,index] using cell (some 3)
  have nBound : count ≤ size frame := by simpa [RegisterRange.bank_at,stored] using cell (some 10)
  have product := Nat.mul_le_mul wBound (Nat.add_le_add_right (Nat.mul_le_mul_left 4 nBound) 10)
  have identity : size frame*(4*size frame+10)+6*size frame+17=4*(size frame)^2+16*size frame+17 := by ring
  have bounded : ticks ≤ 4*(size frame)^2+16*size frame+17 := by rw [← identity]; omega
  have space := trace.peak_le
  change peak ≤ size frame+ticks at space
  exact ⟨ticks,peak,trace,bounded,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 360 := by
  simpa only [Fintype.card_sum,Fintype.card_fin,Fintype.card_option,WordBound.Label,WordBound.BodyLabel,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.IndexRange
