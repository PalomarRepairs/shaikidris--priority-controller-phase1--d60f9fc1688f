module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceLookupTrace
public import Controller.Complexity.SpaceErase
public import Controller.Complexity.SpaceHome

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Executed setup for an intermediate-output request. Left work banks hold
the first transducer and lookup scratch; right banks retain the caller's
state, including its canonical saved request. Every left bank is erased,
the request is copied without consuming its saved value, and input is rewound.
All discarded/copied bits and every retained caller bank are charged. -/
namespace Controller.Complexity.SpaceRequestSetup
open SpaceMachine

abbrev Bank (K J : Type) := SpaceLookup.Bank K ⊕ J
abbrev Label (n : Nat) := (SpaceErase.Label n ⊕ SpaceBuffers.CopyLabel) ⊕ Fin 3

def targets (enumeration : Fin n ≃ SpaceLookup.Bank K) : Fin n ↪ Bank K J where
  toFun index := .inl (enumeration index)
  inj' := by intro first second same; exact enumeration.injective (Sum.inl.inj same)

def copyPorts (request : J) : Option Bool ↪ Bank K J :=
  SpaceWork.threePorts (.inr request) (.inl SpaceLookup.counter) (.inl SpaceLookup.scratch)
    (by simp) (by simp) (by simp [SpaceLookup.counter,SpaceLookup.scratch])

def program (enumeration : Fin n ≃ SpaceLookup.Bank K) (request : J) : SpaceMachine.Program (Bank K J) (Label n) :=
  SpaceLink.program
    (SpaceLink.program (SpaceErase.program (targets (J:=J) enumeration)) (SpaceBuffers.copyProgram (copyPorts request)))
    (SpaceHome.program (K:=Bank K J))

theorem label_card (n : Nat) : Fintype.card (Label n)=2*n+15 := by
  simp [Label,SpaceBuffers.CopyLabel]
  omega

def caller (bank : Bank K J → List Bool) (port : J) := bank (.inr port)
def readyWork (bank : Bank K J → List Bool) (number : Nat) : Bank K J → List Bool :=
  Sum.elim (SpaceLookup.work (fun _ => []) number.bits []) (caller bank)

theorem ready_mass [Fintype K] [Fintype J] (bank : Bank K J → List Bool) (number : Nat) :
    SpaceBuffers.mass (readyWork bank number)=SpaceBuffers.mass (caller bank)+number.bits.length := by
  simp [SpaceBuffers.mass,readyWork,SpaceLookup.work,Fintype.sum_sum_type,Fin.sum_univ_three,SpaceLookup.frame,Nat.add_comm]

theorem execution [Fintype K] [Fintype J] [DecidableEq K] [DecidableEq J]
    (enumeration : Fin n ≃ SpaceLookup.Bank K) (request : J)
    (input : SpaceMachine.State (Bank K J) (Label n))
    (entry : input.pc=some (program enumeration request).main)
    (number : Nat) (encoded : input.work (.inr request)=number.bits) :
    ∃ ticks, SpaceMachine.Execution (program enumeration request) input
      ⟨none,ReadOnlyInput.start (ReadOnlyInput.word input.tape),readyWork input.work number,input.output⟩ ticks
      (max (workspace input) (SpaceBuffers.mass (caller input.work)+number.bits.length)) ∧
      ticks ≤ workspace input+2*n+5*number.bits.length+2*input.tape.left.length+7 := by
  let clearedBank : Bank K J → List Bool := Sum.elim (fun _ => []) (caller input.work)
  let eraseInput : SpaceMachine.State (Bank K J) (SpaceErase.Label n) :=
    ⟨some (SpaceErase.program (targets (J:=J) enumeration)).main,input.tape,input.work,input.output⟩
  obtain ⟨erased,eraseTicks,erasing,cleared,retained,eraseTime⟩ :=
    SpaceErase.execution (targets (J:=J) enumeration) eraseInput rfl
  have erasedEq : erased=clearedBank := by
    funext port
    cases port with
    | inl port =>
      change erased (.inl port)=[]
      have selected := cleared (enumeration.symm port)
      change erased (.inl (enumeration (enumeration.symm port)))=[] at selected
      simpa only [Equiv.apply_symm_apply] using selected
    | inr port =>
      exact retained (.inr port) (by intro selected; simp [targets])
  rw [erasedEq] at erasing
  let copyInput : SpaceMachine.State (Bank K J) SpaceBuffers.CopyLabel :=
    ⟨some (SpaceBuffers.copyProgram (copyPorts (K:=K) request)).main,input.tape,clearedBank,input.output⟩
  have clean : copyInput.work (copyPorts (K:=K) request (some true))=[] := rfl
  obtain ⟨copyPeak,copying,copySpace⟩ := SpaceBuffers.copy_execution (copyPorts request) copyInput rfl clean
  have saved : copyInput.work (copyPorts (K:=K) request none)=number.bits := encoded
  have copyWork : Function.update copyInput.work (copyPorts (K:=K) request (some false))
      (copyInput.work (copyPorts (K:=K) request none)++copyInput.work (copyPorts (K:=K) request (some false)))=
      readyWork input.work number := by
    rw [saved]
    have emptyDestination : copyInput.work (copyPorts (K:=K) request (some false))=[] := rfl
    rw [emptyDestination,List.append_nil]
    change Function.update clearedBank (.inl SpaceLookup.counter) number.bits=readyWork input.work number
    funext port
    cases port with
    | inl port => cases port with
      | inl port => simp [clearedBank,readyWork,SpaceLookup.work,SpaceLookup.counter]
      | inr slot => fin_cases slot <;>
          simp [clearedBank,readyWork,SpaceLookup.work,SpaceLookup.frame,SpaceLookup.counter]
    | inr port => simp [clearedBank,readyWork]
  rw [copyWork,saved] at copying
  have copyMass : workspace copyInput=SpaceBuffers.mass (caller input.work) := by
    simp [workspace,copyInput,clearedBank,SpaceBuffers.mass,Fintype.sum_sum_type]
  rw [copyMass,saved] at copySpace
  let homeInput : SpaceMachine.State (Bank K J) (Fin 3) :=
    ⟨some (SpaceHome.program (K:=Bank K J)).main,input.tape,readyWork input.work number,input.output⟩
  have homing := SpaceHome.execution homeInput rfl
  have complete := SpaceLink.execution (SpaceLink.execution erasing copying) homing
  have ready : (⟨some (program enumeration request).main,input.tape,input.work,input.output⟩ : SpaceMachine.State (Bank K J) (Label n))=input := by
    cases input with
    | mk pc tape bank output => cases entry; rfl
  change SpaceMachine.Execution (program enumeration request)
    ⟨some (program enumeration request).main,input.tape,input.work,input.output⟩
    ⟨none,ReadOnlyInput.start (ReadOnlyInput.word input.tape),readyWork input.work number,input.output⟩
    (eraseTicks+(5*number.bits.length+4)+(2*input.tape.left.length+2))
    (max (max (workspace eraseInput) copyPeak) (workspace homeInput)) at complete
  rw [ready] at complete
  have oldMass : workspace eraseInput=workspace input := rfl
  have homeMass : workspace homeInput=SpaceBuffers.mass (caller input.work)+number.bits.length :=
    ready_mass input.work number
  rw [oldMass,copySpace,homeMass,Nat.max_assoc,Nat.max_self] at complete
  refine ⟨_,complete,?_⟩
  change eraseTicks ≤ workspace input+2*n+1 at eraseTime
  omega

end Controller.Complexity.SpaceRequestSetup
