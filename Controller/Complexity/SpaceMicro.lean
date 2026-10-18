module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceFootprint

@[expose] public section

/-! Internal execution of literal TM2 statements, including every primitive
stack update and branch. The annotated evaluator agrees with library stepAux;
its trace charges maximum lengths in every designated work bank. -/
namespace Controller.Complexity.SpaceMicro
open SpaceMachine

abbrev Storage (K : Type) := SpaceTM.Port K → List Bool
abbrev Statement (K Q : Type) := Turing.TM2.Stmt (fun _ : SpaceTM.Port K => Bool) Q (Option Bool)
abbrev Configuration (K Q : Type) := Turing.TM2.Cfg (fun _ : SpaceTM.Port K => Bool) Q (Option Bool)

inductive State (K Q : Type)
  | pending (code : Statement K Q) (register : Option Bool) (storage : Storage K)
  | done (configuration : Configuration K Q)

def storage : State K Q → Storage K
  | .pending _ _ values => values
  | .done final => final.stk

def tick [DecidableEq K] : State K Q → Option (State K Q)
  | .pending (.push port value next) register bank =>
      some (.pending next register (Function.update bank port (value register :: bank port)))
  | .pending (.peek port value next) register bank => some (.pending next (value register (bank port).head?) bank)
  | .pending (.pop port value next) register bank =>
      some (.pending next (value register (bank port).head?) (Function.update bank port (bank port).tail))
  | .pending (.load value next) register bank => some (.pending next (value register) bank)
  | .pending (.branch test yes no) register bank => some (.pending (cond (test register) yes no) register bank)
  | .pending (.goto next) register bank => some (.done ⟨some (next register),register,bank⟩)
  | .pending .halt register bank => some (.done ⟨none,register,bank⟩)
  | .done _ => none

inductive Trace [DecidableEq K] : State K Q → State K Q → Nat → (K → Nat) → Prop
  | refl (state) : Trace state state 0 (fun port => (storage state (SpaceTM.workPort port)).length)
  | cons {state next final ticks spans} : tick state=some next → Trace next final ticks spans →
      Trace state final (ticks+1) (fun port => max (storage state (SpaceTM.workPort port)).length (spans port))

structure Result (K Q : Type) where
  configuration : Configuration K Q
  ticks : Nat
  spans : K → Nat

def prepend (bank : Storage K) (result : Result K Q) : Result K Q :=
  ⟨result.configuration,result.ticks+1,fun port => max (bank (SpaceTM.workPort port)).length (result.spans port)⟩

def run [DecidableEq K] : Statement K Q → Option Bool → Storage K → Result K Q
  | .push port value next,register,bank => prepend bank (run next register (Function.update bank port (value register :: bank port)))
  | .peek port value next,register,bank => prepend bank (run next (value register (bank port).head?) bank)
  | .pop port value next,register,bank => prepend bank (run next (value register (bank port).head?) (Function.update bank port (bank port).tail))
  | .load value next,register,bank => prepend bank (run next (value register) bank)
  | .branch test yes no,register,bank => prepend bank (cond (test register) (run yes register bank) (run no register bank))
  | .goto next,register,bank => ⟨⟨some (next register),register,bank⟩,1,fun port => (bank (SpaceTM.workPort port)).length⟩
  | .halt,register,bank => ⟨⟨none,register,bank⟩,1,fun port => (bank (SpaceTM.workPort port)).length⟩

theorem configuration_eq [DecidableEq K] (code : Statement K Q) (register : Option Bool) (bank : Storage K) :
    (run code register bank).configuration=Turing.TM2.stepAux code register bank := by
  induction code generalizing register bank with
  | push port value next ih => exact ih _ _
  | peek port value next ih => exact ih _ _
  | pop port value next ih => exact ih _ _
  | load value next ih => exact ih _ _
  | branch test yes no yesIH noIH =>
    cases flag : test register <;> simp [run,prepend,Turing.TM2.stepAux,flag,yesIH,noIH]
  | goto next => rfl
  | halt => rfl

theorem execution [DecidableEq K] (code : Statement K Q) (register : Option Bool) (bank : Storage K) :
    Trace (.pending code register bank) (.done (run code register bank).configuration)
      (run code register bank).ticks (run code register bank).spans := by
  induction code generalizing register bank with
  | push port value next ih => exact Trace.cons rfl (ih _ _)
  | peek port value next ih => exact Trace.cons rfl (ih _ _)
  | pop port value next ih => exact Trace.cons rfl (ih _ _)
  | load value next ih => exact Trace.cons rfl (ih _ _)
  | branch test yes no yesIH noIH =>
    cases flag : test register with
    | false =>
      have path := Trace.cons (show tick (.pending (.branch test yes no) register bank)=some (.pending no register bank) by simp [tick,flag]) (noIH register bank)
      simpa only [run,prepend,flag,Bool.cond_false,storage] using path
    | true =>
      have path := Trace.cons (show tick (.pending (.branch test yes no) register bank)=some (.pending yes register bank) by simp [tick,flag]) (yesIH register bank)
      simpa only [run,prepend,flag,Bool.cond_true,storage] using path
  | goto next =>
    simpa only [run,storage,Nat.max_self] using Trace.cons
      (show tick (.pending (.goto next) register bank)=some (.done ⟨some (next register),register,bank⟩) from rfl)
      (Trace.refl (.done ⟨some (next register),register,bank⟩))
  | halt =>
    simpa only [run,storage,Nat.max_self] using Trace.cons
      (show tick (.pending (.halt : Statement K Q) register bank)=some (.done ⟨none,register,bank⟩) from rfl)
      (Trace.refl (.done ⟨none,register,bank⟩))

theorem ticks_le_depth [DecidableEq K] (code : Statement K Q) (register : Option Bool) (bank : Storage K) :
    (run code register bank).ticks ≤ StackMachine.statementDepth code := by
  induction code generalizing register bank with
  | push port value next ih =>
    simpa only [run,prepend,StackMachine.statementDepth,Nat.add_comm] using
      Nat.add_le_add_right (ih register (Function.update bank port (value register :: bank port))) 1
  | peek port value next ih =>
    simpa only [run,prepend,StackMachine.statementDepth,Nat.add_comm] using
      Nat.add_le_add_right (ih (value register (bank port).head?) bank) 1
  | pop port value next ih =>
    simpa only [run,prepend,StackMachine.statementDepth,Nat.add_comm] using
      Nat.add_le_add_right (ih (value register (bank port).head?) (Function.update bank port (bank port).tail)) 1
  | load value next ih =>
    simpa only [run,prepend,StackMachine.statementDepth,Nat.add_comm] using Nat.add_le_add_right (ih (value register) bank) 1
  | branch test yes no yesIH noIH =>
    have yesBound := yesIH register bank
    have noBound := noIH register bank
    cases flag : test register <;> simp only [run,prepend,flag,Bool.cond_false,Bool.cond_true,StackMachine.statementDepth] <;> omega
  | goto next => rfl
  | halt => rfl

theorem library_execution [DecidableEq K] (code : Statement K Q) (register : Option Bool) (bank : Storage K) :
    Trace (.pending code register bank) (.done (Turing.TM2.stepAux code register bank))
      (run code register bank).ticks (run code register bank).spans := by
  simpa only [configuration_eq] using execution code register bank

end Controller.Complexity.SpaceMicro
