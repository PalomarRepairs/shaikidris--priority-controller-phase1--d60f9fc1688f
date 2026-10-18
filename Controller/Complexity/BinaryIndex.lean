module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.BinaryUnary

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A preserved little-endian index is copied, reversed, and converted to a
unary traversal counter. The execution bound depends on the decoded value;
callers range-check that value against a stored list length before entry. -/
namespace Controller.Complexity.BinaryIndex
open StackMachine StackBlocks WordReader
open scoped BigOperators
abbrev bank := BinaryUnary.bank

def copyPorts : Option Bool ↪ Port := StackFrames.threePorts (some 3) (some 6) (some 17) (by decide) (by decide) (by decide)
def reversePorts : Option Bool ↪ Port := StackFrames.threePorts (some 6) (some 5) (some 17) (by decide) (by decide) (by decide)

theorem copyPorts_apply (port : Option Bool) : copyPorts port=(match port with | none => some 3 | some false => some 6 | some true => some 17) := rfl
theorem reversePorts_apply (port : Option Bool) : reversePorts port=(match port with | none => some 6 | some false => some 5 | some true => some 17) := rfl

def copyMachine := StackFrames.relocate copyPorts StackCopy.program
def reverseMachine := StackFrames.relocate reversePorts reverseProgram
def program := link (link copyMachine reverseMachine) BinaryUnary.program

theorem copy_execution (frame : Port → List Bool) (word : List Bool) (stored : frame (some 3)=word) :
    ∃ peak, Execution copyMachine ⟨some copyMachine.main,bank frame [] 0 [] [] []⟩
      ⟨none,bank frame word 0 [] [] []⟩ (5*word.length+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution copyPorts (bank frame [] 0 [] [] []) (by simp [copyPorts_apply,BinaryUnary.bank_at])
  have output : Function.update (bank frame [] 0 [] [] []) (copyPorts (some false))
      (bank frame [] 0 [] [] [] (copyPorts none)++bank frame [] 0 [] [] [] (copyPorts (some false)))=bank frame word 0 [] [] [] := by
    funext address
    by_cases same : address=some 6 <;> simp_all [copyPorts_apply,BinaryUnary.bank_at]
  rw [output] at trace
  exact ⟨peak,by simpa [copyMachine,StackFrames.relocate,copyPorts_apply,BinaryUnary.bank_at,stored] using trace⟩

theorem reverse_storage (frame : Port → List Bool) (word temporary scratch : List Bool) :
    StackFrames.embedStorage reversePorts (bank frame [] 0 [] [] []) (layout word temporary scratch)=
      bank frame word 0 temporary [] scratch := by
  funext address
  by_cases hw : address=some 6 <;> by_cases ht : address=some 5 <;> by_cases hs : address=some 17 <;>
    simp_all [StackFrames.embedStorage,reversePorts_apply,layout,BinaryUnary.bank_at]

theorem reverse_execution (frame : Port → List Bool) (word : List Bool) :
    ∃ peak, Execution reverseMachine ⟨some reverseMachine.main,bank frame word 0 [] [] []⟩
      ⟨none,bank frame word.reverse 0 [] [] []⟩ (6*word.length+6) peak := by
  have trace := StackFrames.reversal reversePorts (bank frame [] 0 [] [] []) word
  exact ⟨_,by simpa only [reverseMachine,StackFrames.relocate,StackFrames.embedState,initial_layout,terminal_layout,reverse_storage] using trace⟩

theorem execution (frame : Port → List Bool) (word : List Bool) (stored : frame (some 3)=word) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] 0 [] [] []⟩
      ⟨none,bank frame [] (Encoding.value word) [] [] []⟩ ticks peak ∧
      ticks ≤ word.length*(7*Encoding.value word+23)+12 := by
  obtain ⟨copyPeak,copying⟩ := copy_execution frame word stored
  obtain ⟨reversePeak,reversing⟩ := reverse_execution frame word
  obtain ⟨coreTicks,corePeak,converting,coreBound⟩ := BinaryUnary.execution frame word.reverse 0
  have decoded : BinaryUnary.fold 0 word.reverse=Encoding.value word := by simp [BinaryUnary.fold_value]
  rw [decoded,List.length_reverse] at coreBound
  rw [decoded] at converting
  have trace := (copying.link reversing).link converting
  have identity : (5*word.length+4)+(6*word.length+6)+(word.length*(7*Encoding.value word+12)+2)=
      word.length*(7*Encoding.value word+23)+12 := by ring
  exact ⟨_,_,trace,by omega⟩

theorem ready_execution (input : Port → List Bool) (word : List Bool) (stored : input (some 3)=word)
    (counter : input (some 4)=[]) (temporary : input (some 5)=[]) (working : input (some 6)=[])
    (mode : input (some 7)=[]) (scratch : input (some 17)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩
      ⟨none,Function.update input (some 4) (List.replicate (Encoding.value word) true)⟩ ticks peak ∧
      ticks ≤ word.length*(7*Encoding.value word+23)+12 := by
  have entry : bank input [] 0 [] [] []=input := by
    funext address
    by_cases hc : address=some 4 <;> by_cases ht : address=some 5 <;> by_cases hw : address=some 6 <;>
      by_cases hm : address=some 7 <;> by_cases hs : address=some 17 <;> simp_all [BinaryUnary.bank_at]
  have output : bank input [] (Encoding.value word) [] [] []=
      Function.update input (some 4) (List.replicate (Encoding.value word) true) := by
    funext address
    by_cases hc : address=some 4 <;> by_cases ht : address=some 5 <;> by_cases hw : address=some 6 <;>
      by_cases hm : address=some 7 <;> by_cases hs : address=some 17 <;> simp_all [BinaryUnary.bank_at]
  simpa only [entry,output] using execution input word stored

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 396 := by
  simpa only [program,copyMachine,reverseMachine,StackFrames.relocate,StackCopy.program,reverseProgram,
    Fintype.card_sum,Fintype.card_fin,Fintype.card_option,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.BinaryIndex
