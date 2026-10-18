module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.RegisterCapacity
public import Controller.Complexity.IndexRange

public import Mathlib.Tactic.Ring

@[expose] public section

/-! The actual saved list count is checked strictly below binary word capacity.
Copied count10 and copied unary width8 drive the all-ones halving test. Originals
are preserved, work is cleared and no unary counter of length `2^width` is built. -/
namespace Controller.Complexity.HeapCapacity
open StackMachine WordReader
open scoped BigOperators
abbrev bank := RegisterRange.bank

def program := link (link (link IndexRange.countMachine RegisterCapacity.widthMachine) RegisterRange.coreMachine) RegisterCapacity.invertProgram

theorem capacity_test (width count : Nat) : Encoding.value (List.replicate width true)<count ↔ ¬count<2^width := by
  have value := RegisterCapacity.ones_value width
  omega

theorem execution (frame : Port → List Bool) (width count : Nat)
    (widthStored : frame (some 8)=List.replicate width true) (countStored : frame (some 10)=List.replicate count true) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] [] [] []⟩
      ⟨none,bank frame (if count<2^width then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ width*(4*count+10)+6*count+16 := by
  obtain ⟨copyPeak,copying⟩ := IndexRange.count_execution frame [] count countStored
  obtain ⟨widthPeak,widthRun⟩ := RegisterCapacity.width_execution frame width count widthStored
  obtain ⟨coreTicks,corePeak,checking,coreBound⟩ := RegisterRange.core_execution frame (List.replicate width true) count
  have flag : (if Encoding.value (List.replicate width true)<count then [] else [false])=
      (if count<2^width then [false] else []) := by
    have equivalence := capacity_test width count
    by_cases valid : count<2^width <;> simp_all
  rw [flag] at checking
  obtain ⟨invertTicks,invertPeak,inverting,invertBound⟩ := RegisterCapacity.invert_execution frame (count<2^width)
  have trace := ((copying.link widthRun).link checking).link inverting
  simp only [List.length_replicate] at coreBound
  have identity : (5*count+4)+(5*width+4)+(width*(4*count+5)+count+5)+3=width*(4*count+10)+6*count+16 := by ring
  exact ⟨_,_,trace,by omega⟩

theorem ready_execution (input : Port → List Bool) (width count : Nat)
    (widthStored : input (some 8)=List.replicate width true) (countStored : input (some 10)=List.replicate count true)
    (status : input none=[]) (word : input (some 1)=[]) (bound : input (some 16)=[]) (scratch : input (some 17)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩
      ⟨none,Function.update input none (if count<2^width then [] else [false])⟩ ticks peak ∧
      ticks ≤ width*(4*count+10)+6*count+16 := by
  have entry : bank input [] [] [] []=input := by
    funext address
    by_cases hc : address=none <;> by_cases hw : address=some 1 <;> by_cases hb : address=some 16 <;>
      by_cases hs : address=some 17 <;> simp_all [RegisterRange.bank_at]
  have output (flag : List Bool) : bank input flag [] [] []=Function.update input none flag := by
    funext address
    by_cases hc : address=none <;> by_cases hw : address=some 1 <;> by_cases hb : address=some 16 <;>
      by_cases hs : address=some 17 <;> simp_all [RegisterRange.bank_at]
  simpa only [entry,output] using execution input width count widthStored countStored

def size (input : Port → List Bool) : Nat := ∑ port : Port,(input port).length

theorem total_polynomial (input : Port → List Bool) (width count : Nat)
    (widthStored : input (some 8)=List.replicate width true) (countStored : input (some 10)=List.replicate count true)
    (status : input none=[]) (word : input (some 1)=[]) (bound : input (some 16)=[]) (scratch : input (some 17)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩
      ⟨none,Function.update input none (if count<2^width then [] else [false])⟩ ticks peak ∧
      ticks ≤ 4*(size input)^2+16*size input+16 ∧ peak ≤ 4*(size input)^2+17*size input+16 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := ready_execution input width count widthStored countStored status word bound scratch
  have cell (port : Port) : (input port).length ≤ size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have wBound : width ≤ size input := by simpa only [widthStored,List.length_replicate] using cell (some 8)
  have nBound : count ≤ size input := by simpa only [countStored,List.length_replicate] using cell (some 10)
  have product := Nat.mul_le_mul wBound (Nat.add_le_add_right (Nat.mul_le_mul_left 4 nBound) 10)
  have identity : size input*(4*size input+10)+6*size input+16=4*(size input)^2+16*size input+16 := by ring
  have bounded : ticks ≤ 4*(size input)^2+16*size input+16 := by rw [← identity]; omega
  have space := trace.peak_le
  change peak ≤ size input+ticks at space
  exact ⟨ticks,peak,trace,bounded,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 351 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul,WordBound.Label,WordBound.BodyLabel] using finiteTM_resident program

end Controller.Complexity.HeapCapacity
