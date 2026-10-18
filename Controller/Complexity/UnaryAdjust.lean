module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.FieldSetNative

@[expose] public section

/-! Executed unary list-count adjustment and source-preserving traversal-count
setup. Removing a positive count consumes exactly one true cell; removing an
empty count publishes failure without changing any other bank. -/
namespace Controller.Complexity.UnaryAdjust
open StackMachine WordReader
open scoped BigOperators

def increment : Program (Fin 31) (Fin 2) where
  main := 0
  code label := if label=0 then .push (some 10) true 1 else .halt

def decrement : Program (Fin 31) (Fin 3) where
  main := 0
  code label := match label.val with
    | 0 => .pop (some 10) 1 1 2
    | 1 => .push none false 2
    | _ => .halt

theorem increment_execution (input : Port → List Bool) (count : Nat) (stored : input (some 10)=List.replicate count true) :
    ∃ peak, Execution increment ⟨some increment.main,input⟩
      ⟨none,Function.update input (some 10) (List.replicate (count+1) true)⟩ 2 peak := by
  have first : step increment ⟨some increment.main,input⟩=
      some ⟨some 1,Function.update input (some 10) (List.replicate (count+1) true)⟩ := by
    simp [step,increment,instructionStep,stored,List.replicate_succ]
  have last : step increment ⟨some 1,Function.update input (some 10) (List.replicate (count+1) true)⟩=
      some ⟨none,Function.update input (some 10) (List.replicate (count+1) true)⟩ := rfl
  exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩

theorem decrement_success (input : Port → List Bool) (count : Nat) (stored : input (some 10)=List.replicate (count+1) true) :
    ∃ peak, Execution decrement ⟨some decrement.main,input⟩
      ⟨none,Function.update input (some 10) (List.replicate count true)⟩ 2 peak := by
  have first : step decrement ⟨some decrement.main,input⟩=
      some ⟨some 2,Function.update input (some 10) (List.replicate count true)⟩ := by
    simp [step,decrement,instructionStep,stored,List.replicate_succ]
  have last : step decrement ⟨some 2,Function.update input (some 10) (List.replicate count true)⟩=
      some ⟨none,Function.update input (some 10) (List.replicate count true)⟩ := rfl
  exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩

theorem decrement_empty (input : Port → List Bool) (stored : input (some 10)=[]) :
    ∃ peak, Execution decrement ⟨some decrement.main,input⟩
      ⟨none,Function.update input none (false :: input none)⟩ 3 peak := by
  have cleaned : Function.update input (some 10) []=input := by
    funext address
    by_cases same : address=some 10 <;> simp_all
  have first : step decrement ⟨some decrement.main,input⟩=some ⟨some 1,input⟩ := by
    simp [step,decrement,instructionStep,stored,cleaned]
  have middle : step decrement ⟨some 1,input⟩=some ⟨some 2,Function.update input none (false :: input none)⟩ := rfl
  have last : step decrement ⟨some 2,Function.update input none (false :: input none)⟩=
      some ⟨none,Function.update input none (false :: input none)⟩ := rfl
  exact ⟨_,Execution.cons first (Execution.cons middle (Execution.cons last (Execution.refl _)))⟩

def copyPorts : Option Bool ↪ Port := StackFrames.threePorts (some 10) (some 4) (some 2) (by decide) (by decide) (by decide)

theorem copyPorts_apply (port : Option Bool) : copyPorts port=(match port with | none => some 10 | some false => some 4 | some true => some 2) := rfl

def copyCounter := StackFrames.relocate copyPorts StackCopy.program

theorem copy_execution (input : Port → List Bool) (count : Nat)
    (stored : input (some 10)=List.replicate count true) (counter : input (some 4)=[]) (scratch : input (some 2)=[]) :
    ∃ peak, Execution copyCounter ⟨some copyCounter.main,input⟩
      ⟨none,Function.update input (some 4) (List.replicate count true)⟩ (5*count+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution copyPorts input (by simpa only [copyPorts_apply] using scratch)
  exact ⟨peak,by simpa only [copyCounter,StackFrames.relocate,copyPorts_apply,stored,counter,List.append_nil,List.length_replicate] using trace⟩

theorem increment_resident : (∑ label, statementSize (tmStatement (increment.code label))) ≤ 18 := by
  simpa only [Fintype.card_fin,Nat.reduceMul] using finiteTM_resident increment

theorem decrement_resident : (∑ label, statementSize (tmStatement (decrement.code label))) ≤ 27 := by
  simpa only [Fintype.card_fin,Nat.reduceMul] using finiteTM_resident decrement

theorem copy_resident : (∑ label, statementSize (tmStatement (copyCounter.code label))) ≤ 90 := by
  simpa only [Fintype.card_sum,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident copyCounter

end Controller.Complexity.UnaryAdjust
