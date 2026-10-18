module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceSuppress
public import Controller.Complexity.SpaceDecrement
public import Mathlib.Algebra.BigOperators.Fin

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Finite output interception for intermediate-bit recomputation. The first
transducer's work banks are separate from a canonical binary countdown,
empty decrement scratch and a one-bit answer. Every skipped emission runs the
physical decrement routine. At countdown zero an emission publishes one bit
and halts; reaching the source halt first leaves the answer empty. External
output is never used for the intermediate stream. -/
namespace Controller.Complexity.SpaceLookup
open SpaceMachine

abbrev Bank (K : Type) := K ⊕ Fin 3
abbrev Label (Q : Type) := Q ⊕ ((Q × Fin 7) ⊕ (Bool ⊕ Unit))
def sourceLabel (label : Q) : Label Q := .inl label
def decrementLabel (next : Q) (label : Fin 7) : Label Q := .inr (.inl (next,label))
def captureLabel (bit : Bool) : Label Q := .inr (.inr (.inl bit))
def done : Label Q := .inr (.inr (.inr ()))
def counter : Bank K := .inr 0
def scratch : Bank K := .inr 1
def answer : Bank K := .inr 2
def ports : Bool ↪ Bank K := SpaceFrames.twoPorts counter scratch (by simp [counter,scratch])

def frame (bits result : List Bool) (port : Fin 3) : List Bool :=
  if port=0 then bits else if port=2 then result else []

def work (bank : K → List Bool) (bits result : List Bool) : Bank K → List Bool :=
  Sum.elim bank (frame bits result)

def view (output : List Bool) (source : SpaceMachine.State K Q) (number : Nat) : SpaceMachine.State (Bank K) (Label Q) :=
  SpaceControl.state sourceLabel none (SpaceSuppress.state (frame number.bits []) output source)

def program (source : SpaceMachine.Program K Q) : SpaceMachine.Program (Bank K) (Label Q) where
  main := sourceLabel source.main
  code label := match label with
    | .inl label => match source.code label with
      | .emit bit next => .peek counter (captureLabel bit)
          (decrementLabel next (SpaceDecrement.program (ports (K:=K))).main)
          (decrementLabel next (SpaceDecrement.program (ports (K:=K))).main)
      | code => SpaceControl.instruction sourceLabel none (SpaceSuppress.instruction code)
    | .inr (.inl (next,label)) =>
        SpaceControl.instruction (decrementLabel next) (some (sourceLabel next)) ((SpaceDecrement.program ports).code label)
    | .inr (.inr (.inl bit)) => .push answer bit done
    | .inr (.inr (.inr ())) => .halt

theorem label_card [Fintype Q] : Fintype.card (Label Q)=8*Fintype.card Q+3 := by
  simp only [Label,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_unit]
  omega

theorem bank_card [Fintype K] : Fintype.card (Bank K)=Fintype.card K+3 := by simp [Bank]

theorem resident [Fintype Q] (source : SpaceMachine.Program K Q) :
    (∑ label, StackMachine.statementSize (SpaceTM.statement ((program source).code label))) ≤ 9*(8*Fintype.card Q+3) := by
  simpa only [label_card] using SpaceTM.resident (program source)

theorem work_counter [DecidableEq K] (bank : K → List Bool) (bits result replacement : List Bool) :
    Function.update (work bank bits result) counter replacement=work bank replacement result := by
  funext port
  cases port with
  | inl port => simp [work,counter]
  | inr port => fin_cases port <;> simp [work,frame,counter]

theorem work_answer [DecidableEq K] (bank : K → List Bool) (bits result replacement : List Bool) :
    Function.update (work bank bits result) answer replacement=work bank bits replacement := by
  funext port
  cases port with
  | inl port => simp [work,answer]
  | inr port => fin_cases port <;> simp [work,frame,answer]

theorem workspace_work [Fintype K] (pc : Option P) (tape : ReadOnlyInput.Tape)
    (bank : K → List Bool) (bits result output : List Bool) :
    workspace (⟨pc,tape,work bank bits result,output⟩ : SpaceMachine.State (Bank K) P)=
      (∑ port, (bank port).length)+bits.length+result.length := by
  simp [workspace,work,Fintype.sum_sum_type,Fin.sum_univ_three,frame,Nat.add_assoc]

theorem workspace_view [Fintype K] (output : List Bool) (source : SpaceMachine.State K Q) (number : Nat) :
    workspace (view output source number)=workspace source+number.bits.length := by
  simpa only [workspace,SpaceControl.state,SpaceSuppress.state,view,work,List.length_nil,Nat.add_zero] using
    workspace_work (source.pc.elim none (some ∘ sourceLabel)) source.tape source.work number.bits [] output

theorem ordinary_step [DecidableEq K] (source : SpaceMachine.Program K Q) (output : List Bool)
    (input : SpaceMachine.State K Q) (label : Q) (number : Nat)
    (position : input.pc=some label) (ordinary : emitted (source.code label)=none) :
    SpaceMachine.step (program source) (view output input number)=
      some (view output (instructionStep (source.code label) input) number) := by
  have code : (program source).code (sourceLabel label)=
      SpaceControl.instruction sourceLabel none (SpaceSuppress.instruction (J:=Fin 3) (source.code label)) := by
    cases instruction : source.code label <;> simp [program,sourceLabel,instruction]
    simp [instruction,emitted] at ordinary
  simp only [SpaceMachine.step,view,SpaceControl.state,SpaceSuppress.state,position,
    Option.elim_some,Function.comp_apply,Option.map_some,code]
  exact congrArg some ((SpaceControl.instruction_step sourceLabel none _ _).trans
    (congrArg (SpaceControl.state sourceLabel none) (SpaceSuppress.instruction_step _ output _ input)))

theorem decrement_execution [Fintype K] [DecidableEq K] (source : SpaceMachine.Program K Q)
    (output : List Bool) (input : SpaceMachine.State K Q) (next : Q) (number : Nat) :
    SpaceMachine.Execution (program source)
      ⟨some (decrementLabel next (SpaceDecrement.program (ports (K:=K))).main),input.tape,work input.work number.bits [],output⟩
      (view output { input with pc := some next } (number-1))
      (BinaryDecrement.cost number.bits) (workspace input+number.bits.length) := by
  let start : SpaceMachine.State (Bank K) (Fin 7) :=
    ⟨some (SpaceDecrement.program (ports (K:=K))).main,input.tape,work input.work number.bits [],output⟩
  have clean : start.work (ports true)=[] := by simp [start,ports,SpaceFrames.twoPorts,work,frame,scratch]
  have actual := SpaceDecrement.execution ports start rfl clean
  have compiled := SpaceControl.execution (SpaceDecrement.program ports) (program source)
    (decrementLabel next) (some (sourceLabel next)) (fun _ => rfl) actual
  have count : start.work (ports false)=number.bits := by simp [start,ports,SpaceFrames.twoPorts,work,frame,counter]
  rw [count,BinaryDecrement.decrement_bits] at compiled
  have finalWork : Function.update start.work (ports false) (number-1).bits=work input.work (number-1).bits [] := by
    change Function.update (work input.work number.bits []) counter (number-1).bits=_
    exact work_counter _ _ _ _
  have mass : workspace start=workspace input+number.bits.length := by
    simpa only [start,workspace,List.length_nil,Nat.add_zero] using
      workspace_work start.pc input.tape input.work number.bits [] output
  rw [finalWork,mass] at compiled
  exact compiled

theorem skip_execution [Fintype K] [DecidableEq K] (source : SpaceMachine.Program K Q)
    (output : List Bool) (input : SpaceMachine.State K Q) (label next : Q) (bit : Bool) (number : Nat)
    (position : input.pc=some label) (code : source.code label=.emit bit next) :
    SpaceMachine.Execution (program source) (view output input (number+1))
      (view output { input with pc := some next } number)
      (BinaryDecrement.cost (number+1).bits+1) (workspace input+(number+1).bits.length) := by
  have nonempty : (number+1).bits ≠ [] := by
    intro empty
    have size := Nat.size_eq_bits_len (number+1)
    rw [empty,List.length_nil] at size
    have zero := Nat.size_eq_zero.mp size.symm
    omega
  have first : SpaceMachine.step (program source) (view output input (number+1))=
      some ⟨some (decrementLabel next (SpaceDecrement.program (ports (K:=K))).main),input.tape,
        work input.work (number+1).bits [],output⟩ := by
    cases bits : (number+1).bits with
    | nil => exact (nonempty bits).elim
    | cons head rest => cases head <;>
        simp [SpaceMachine.step,program,view,SpaceControl.state,SpaceSuppress.state,position,
          sourceLabel,code,instructionStep,advance,observed,counter,frame,work,bits]
  have actual := decrement_execution source output input next (number+1)
  simp only [Nat.add_sub_cancel] at actual
  simpa only [workspace_view,Nat.max_self] using Execution.cons first actual

theorem capture_execution [Fintype K] [DecidableEq K] (source : SpaceMachine.Program K Q)
    (output : List Bool) (input : SpaceMachine.State K Q) (label next : Q) (bit : Bool)
    (position : input.pc=some label) (code : source.code label=.emit bit next) :
    SpaceMachine.Execution (program source) (view output input 0)
      ⟨none,input.tape,work input.work [] [bit],output⟩ 3 (workspace input+1) := by
  let found : SpaceMachine.State (Bank K) (Label Q) :=
    ⟨some (captureLabel bit),input.tape,work input.work [] [],output⟩
  let published : SpaceMachine.State (Bank K) (Label Q) :=
    ⟨some done,input.tape,work input.work [] [bit],output⟩
  let final : SpaceMachine.State (Bank K) (Label Q) :=
    ⟨none,input.tape,work input.work [] [bit],output⟩
  have first : SpaceMachine.step (program source) (view output input 0)=some found := by
    simp [SpaceMachine.step,program,view,SpaceControl.state,SpaceSuppress.state,position,sourceLabel,
      code,instructionStep,advance,observed,counter,frame,work,found,captureLabel]
  have second : SpaceMachine.step (program source) found=some published := by
    change some (⟨some done,input.tape,Function.update (work input.work [] []) answer
      (bit :: work input.work [] [] answer),output⟩ : SpaceMachine.State (Bank K) (Label Q))=some published
    have empty : work input.work [] [] answer=[] := rfl
    rw [empty,work_answer]
  have third : SpaceMachine.step (program source) published=some final := by
    simp only [SpaceMachine.step,published,done,program,Option.map_some,instructionStep,final]
  have actual := Execution.cons first (Execution.cons second (Execution.cons third (Execution.refl final)))
  have initialMass : workspace (view output input 0)=workspace input := by simp [workspace_view]
  have foundMass : workspace found=workspace input := by
    simpa only [found,workspace,List.length_nil,Nat.add_zero] using workspace_work found.pc input.tape input.work [] [] output
  have publishedMass : workspace published=workspace input+1 := by
    simpa only [published,workspace,List.length_nil,List.length_cons,Nat.add_zero,Nat.zero_add] using
      workspace_work published.pc input.tape input.work [] [bit] output
  have finalMass : workspace final=workspace input+1 := publishedMass
  simpa only [initialMass,foundMass,publishedMass,finalMass,Nat.max_self,Nat.max_eq_right (Nat.le_add_right _ _)] using actual

end Controller.Complexity.SpaceLookup
