module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.StackCopy

@[expose] public section

/-! A finite binary-stack routine doubles a unary counter by a preserved
copy and an actual transfer. Both scratch banks start and finish empty. -/
namespace Controller.Complexity.UnaryDouble
open StackMachine StackBlocks
open scoped BigOperators

def program := link StackCopy.program (transfer (K := Bool) (some false) none)

theorem transfer_storage (base count temporary : List Bool) :
    storage (layout base [] []) (some false) none temporary count=layout count temporary [] := by
  funext port
  cases port with
  | none => simp [storage,layout]
  | some bit => cases bit <;> simp [storage,layout]

theorem exact_execution (count : Nat) :
    Execution program ⟨some program.main,layout (List.replicate count true) [] []⟩
      ⟨none,layout (List.replicate (2*count) true) [] []⟩ (7*count+6) (2*count) := by
  have copying := StackCopy.execution (List.replicate count true) []
  simp only [List.append_nil,List.length_replicate] at copying
  have moving := transfer_execution (layout (List.replicate count true) [] []) (source := some false) (destination := none)
    (by decide) (List.replicate count true) (List.replicate count true)
  simp only [state,transfer_storage,List.reverse_replicate,List.length_replicate] at moving
  have trace := copying.link moving
  have length : 2*count=count+count := by omega
  have ticks : (5*count+4)+(2*count+2)=7*count+6 := by omega
  rw [ticks] at trace
  simp only [live_layout,List.length_replicate,List.length_nil,Nat.add_zero] at trace
  have peak : max (2*count) (count+count)=2*count := by omega
  rw [peak] at trace
  simpa only [program,length,List.replicate_add] using trace

theorem execution (count : Nat) :
    ∃ peak, Execution program ⟨some program.main,layout (List.replicate count true) [] []⟩
      ⟨none,layout (List.replicate (2*count) true) [] []⟩ (7*count+6) peak := ⟨2*count,exact_execution count⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 126 := by
  simpa only [Fintype.card_sum,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.UnaryDouble
