module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.UnaryEqual
public import Controller.Complexity.StackCopy
public import Controller.Complexity.WordReader

@[expose] public section

/-! Parsed field counts are compared with the saved register count. Both
inputs are copied by executed source-preserving routines; the comparison
clears its work banks and publishes an actual canonical status. -/
namespace Controller.Complexity.CountEquality
open StackMachine WordReader
open scoped BigOperators

def bank (frame : Port → List Bool) (status left right : List Bool) : Port → List Bool :=
  Function.update (Function.update (Function.update frame none status) (some 16) left) (some 17) right

theorem bank_at (frame : Port → List Bool) (status left right : List Bool) (address : Port) :
    bank frame status left right address=
      if address=some 17 then right else if address=some 16 then left else if address=none then status else frame address := by
  simp only [bank,Function.update_apply]

def leftPorts : Option Bool ↪ Port := StackFrames.threePorts (some 9) (some 16) (some 20) (by decide) (by decide) (by decide)
def rightPorts : Option Bool ↪ Port := StackFrames.threePorts (some 12) (some 17) (some 20) (by decide) (by decide) (by decide)
def comparePorts : Option Bool ↪ Port := StackFrames.threePorts (some 16) (some 17) none (by decide) (by decide) (by decide)

theorem leftPorts_apply (port : Option Bool) : leftPorts port=(match port with | none => some 9 | some false => some 16 | some true => some 20) := rfl
theorem rightPorts_apply (port : Option Bool) : rightPorts port=(match port with | none => some 12 | some false => some 17 | some true => some 20) := rfl
theorem comparePorts_apply (port : Option Bool) : comparePorts port=(match port with | none => some 16 | some false => some 17 | some true => none) := rfl

def leftMachine := StackFrames.relocate leftPorts StackCopy.program
def rightMachine := StackFrames.relocate rightPorts StackCopy.program
def compareMachine := StackFrames.relocate comparePorts UnaryEqual.program
def program := link (link leftMachine rightMachine) compareMachine

theorem left_execution (frame : Port → List Bool) (count : Nat) (stored : frame (some 9)=List.replicate count true)
    (scratch : frame (some 20)=[]) :
    ∃ peak, Execution leftMachine ⟨some leftMachine.main,bank frame [] [] []⟩
      ⟨none,bank frame [] (List.replicate count true) []⟩ (5*count+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution leftPorts (bank frame [] [] []) (by simp [leftPorts_apply,bank_at,scratch])
  have output : Function.update (bank frame [] [] []) (leftPorts (some false))
      (bank frame [] [] [] (leftPorts none)++bank frame [] [] [] (leftPorts (some false)))=
      bank frame [] (List.replicate count true) [] := by
    funext address
    by_cases same : address=some 16 <;> simp_all [leftPorts_apply,bank_at]
  rw [output] at trace
  exact ⟨peak,by simpa [leftMachine,StackFrames.relocate,leftPorts_apply,bank_at,stored] using trace⟩

theorem right_execution (frame : Port → List Bool) (left count : Nat) (stored : frame (some 12)=List.replicate count true)
    (scratch : frame (some 20)=[]) :
    ∃ peak, Execution rightMachine ⟨some rightMachine.main,bank frame [] (List.replicate left true) []⟩
      ⟨none,bank frame [] (List.replicate left true) (List.replicate count true)⟩ (5*count+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution rightPorts (bank frame [] (List.replicate left true) []) (by simp [rightPorts_apply,bank_at,scratch])
  have output : Function.update (bank frame [] (List.replicate left true) []) (rightPorts (some false))
      (bank frame [] (List.replicate left true) [] (rightPorts none)++bank frame [] (List.replicate left true) [] (rightPorts (some false)))=
      bank frame [] (List.replicate left true) (List.replicate count true) := by
    funext address
    by_cases same : address=some 17 <;> simp_all [rightPorts_apply,bank_at]
  rw [output] at trace
  exact ⟨peak,by simpa [rightMachine,StackFrames.relocate,rightPorts_apply,bank_at,stored] using trace⟩

theorem compare_storage (frame : Port → List Bool) (left right status : List Bool) :
    StackFrames.embedStorage comparePorts frame (StackBlocks.layout left right status)=bank frame status left right := by
  funext address
  by_cases hs : address=none <;> by_cases hl : address=some 16 <;> by_cases hr : address=some 17 <;>
    simp_all [StackFrames.embedStorage,comparePorts_apply,StackBlocks.layout,bank_at]

theorem compare_execution (frame : Port → List Bool) (left right : Nat) :
    ∃ ticks peak, Execution compareMachine
      ⟨some compareMachine.main,bank frame [] (List.replicate left true) (List.replicate right true)⟩
      ⟨none,bank frame (if left=right then [] else [false]) [] []⟩ ticks peak ∧ ticks ≤ left+right+6 := by
  obtain ⟨ticks,peak,trace,bound⟩ := UnaryEqual.execution left right
  have relocated := StackFrames.execution comparePorts frame trace
  exact ⟨ticks,_,by simpa only [compareMachine,StackFrames.relocate,StackFrames.embedState,UnaryEqual.state,compare_storage] using relocated,bound⟩

theorem execution (frame : Port → List Bool) (registers count : Nat)
    (stored : frame (some 9)=List.replicate registers true) (parsed : frame (some 12)=List.replicate count true)
    (scratch : frame (some 20)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] [] []⟩
      ⟨none,bank frame (if count=registers then [] else [false]) [] []⟩ ticks peak ∧ ticks ≤ 6*registers+6*count+14 := by
  obtain ⟨leftPeak,copyLeft⟩ := left_execution frame registers stored scratch
  obtain ⟨rightPeak,copyRight⟩ := right_execution frame registers count parsed scratch
  obtain ⟨compareTicks,comparePeak,checking,timeBound⟩ := compare_execution frame registers count
  have trace := (copyLeft.link copyRight).link checking
  have flag : (if registers=count then [] else [false])=(if count=registers then [] else [false]) := by simp only [eq_comm]
  rw [flag] at trace
  exact ⟨_,_,trace,by omega⟩

theorem ready_bank (input : Port → List Bool) (status : input none=[]) (left : input (some 16)=[]) (right : input (some 17)=[]) :
    bank input [] [] []=input := by
  funext address
  by_cases hs : address=none <;> by_cases hl : address=some 16 <;> by_cases hr : address=some 17 <;> simp_all [bank_at]

theorem ready_execution (input : Port → List Bool) (registers count : Nat)
    (status : input none=[]) (left : input (some 16)=[]) (right : input (some 17)=[])
    (stored : input (some 9)=List.replicate registers true) (parsed : input (some 12)=List.replicate count true)
    (scratch : input (some 20)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩
      ⟨none,bank input (if count=registers then [] else [false]) [] []⟩ ticks peak ∧ ticks ≤ 6*registers+6*count+14 := by
  have entry := ready_bank input status left right
  simpa only [entry] using execution input registers count stored parsed scratch

def size (frame : Port → List Bool) : Nat := ∑ port : Port,(bank frame [] [] [] port).length

theorem total_polynomial (frame : Port → List Bool) (registers count : Nat)
    (stored : frame (some 9)=List.replicate registers true) (parsed : frame (some 12)=List.replicate count true)
    (scratch : frame (some 20)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] [] []⟩
      ⟨none,bank frame (if count=registers then [] else [false]) [] []⟩ ticks peak ∧
      ticks ≤ 12*size frame+14 ∧ peak ≤ 13*size frame+14 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution frame registers count stored parsed scratch
  have cell (port : Port) : (bank frame [] [] [] port).length ≤ size frame :=
    Finset.single_le_sum (f := fun address : Port => (bank frame [] [] [] address).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have rb : registers ≤ size frame := by simpa [bank_at,stored] using cell (some 9)
  have cb : count ≤ size frame := by simpa [bank_at,parsed] using cell (some 12)
  have space := trace.peak_le
  change peak ≤ size frame+ticks at space
  exact ⟨ticks,peak,trace,by omega,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 243 := by
  simpa only [Fintype.card_sum,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.CountEquality
