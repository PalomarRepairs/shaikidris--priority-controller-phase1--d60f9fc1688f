module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.FetchSetup

@[expose] public section

/-! Two charged transfers move a bit string without reversing its order.
The source is consumed, the scratch returns empty and the destination retains
its original suffix. Every other physical bank is preserved. -/
namespace Controller.Complexity.WordMove
open StackMachine StackBlocks WordReader
open scoped BigOperators

def program (source destination scratch : Port) := link (transfer source scratch) (transfer scratch destination)

theorem execution (input : Port → List Bool) (source destination scratch : Port)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch) (destinationScratch : destination ≠ scratch)
    (clean : input scratch=[]) :
    ∃ peak, Execution (program source destination scratch) ⟨some (program source destination scratch).main,input⟩
      ⟨none,Function.update (Function.update input source []) destination (input source++input destination)⟩
      (4*(input source).length+4) peak := by
  obtain ⟨firstPeak,first⟩ := InstructionCollect.move_execution input source scratch sourceScratch
  simp only [clean,List.append_nil] at first
  let middle := Function.update (Function.update input source []) scratch (input source).reverse
  obtain ⟨secondPeak,second⟩ := InstructionCollect.move_execution middle scratch destination destinationScratch.symm
  have sourceAt : middle scratch=(input source).reverse := by simp [middle]
  have destinationAt : middle destination=input destination := by simp [middle,destinationScratch,sourceDestination.symm]
  rw [sourceAt,destinationAt,List.reverse_reverse,List.length_reverse] at second
  have output : Function.update (Function.update middle scratch []) destination (input source++input destination)=
      Function.update (Function.update input source []) destination (input source++input destination) := by
    funext address
    by_cases hs : address=source <;> by_cases hd : address=destination <;> by_cases ht : address=scratch <;>
      simp_all [middle]
  rw [output] at second
  have ticks : (2*(input source).length+2)+(2*(input source).length+2)=4*(input source).length+4 := by omega
  exact ⟨_,by simpa only [program,transfer,ticks] using first.link second⟩

theorem resident (source destination scratch : Port) :
    (∑ label, statementSize (tmStatement ((program source destination scratch).code label))) ≤ 72 := by
  simpa only [Fintype.card_sum,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident (program source destination scratch)

end Controller.Complexity.WordMove
