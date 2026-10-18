module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceWork
public import Controller.Complexity.SpaceLink
public import Controller.Complexity.StackCopy

@[expose] public section

/-! Executed work-bank erasure and source-preserving copying. Reset charges
every discarded bit. Copy uses three distinct work ports and retains all
external input/output and unselected work. -/
namespace Controller.Complexity.SpaceBuffers
open SpaceMachine
open scoped BigOperators

def mass [Fintype K] (work : K → List Bool) := ∑ port, (work port).length

theorem mass_update [Fintype K] [DecidableEq K] (work : K → List Bool) (port : K) (bits : List Bool) :
    mass (Function.update work port bits)+(work port).length=mass work+bits.length := by
  have lengths : (fun target => (Function.update work port bits target).length)=
      Function.update (fun target => (work target).length) port bits.length := by
    funext target
    by_cases same : target=port <;> simp [same]
  have original := Finset.sum_update_of_mem (Finset.mem_univ port) (fun target => (work target).length) (work port).length
  simp only [Function.update_eq_self] at original
  simp only [mass,lengths,Finset.sum_update_of_mem (Finset.mem_univ port)]
  omega

def clearProgram (port : K) : SpaceMachine.Program K (Fin 2) where
  main := 0
  code label := if label=0 then .pop port 1 0 0 else .halt

def clearState [DecidableEq K] (tape : ReadOnlyInput.Tape) (output : List Bool) (work : K → List Bool)
    (port : K) (pc : Option (Fin 2)) (bits : List Bool) : SpaceMachine.State K (Fin 2) :=
  ⟨pc,tape,Function.update work port bits,output⟩

theorem clear_workspace [Fintype K] [DecidableEq K] (tape : ReadOnlyInput.Tape) (output : List Bool) (work : K → List Bool)
    (port : K) (pc : Option (Fin 2)) (bits : List Bool) :
    workspace (clearState tape output work port pc bits)=mass (Function.update work port bits) := rfl

theorem clear_empty [DecidableEq K] (tape : ReadOnlyInput.Tape) (output : List Bool) (work : K → List Bool) (port : K) :
    step (clearProgram port) (clearState tape output work port (some 0) [])=
      some (clearState tape output work port (some 1) []) := by
  simp [step,clearProgram,clearState,instructionStep,advance,observed]

theorem clear_pop [DecidableEq K] (tape : ReadOnlyInput.Tape) (output : List Bool) (work : K → List Bool)
    (port : K) (bit : Bool) (bits : List Bool) :
    step (clearProgram port) (clearState tape output work port (some 0) (bit :: bits))=
      some (clearState tape output work port (some 0) bits) := by
  cases bit <;> simp [step,clearProgram,clearState,instructionStep,advance,observed]

theorem clear_halt [DecidableEq K] (tape : ReadOnlyInput.Tape) (output : List Bool) (work : K → List Bool) (port : K) :
    step (clearProgram port) (clearState tape output work port (some 1) [])=
      some (clearState tape output work port none []) := rfl

theorem clear_exact [Fintype K] [DecidableEq K] (tape : ReadOnlyInput.Tape) (output : List Bool)
    (work : K → List Bool) (port : K) (bits : List Bool) :
    SpaceMachine.Execution (clearProgram port) (clearState tape output work port (some (clearProgram port).main) bits)
      (clearState tape output work port none []) (bits.length+2) (mass (Function.update work port bits)) := by
  induction bits with
  | nil =>
    have trace := Execution.cons (clear_empty tape output work port)
      (Execution.cons (clear_halt tape output work port) (Execution.refl _))
    simpa only [clearProgram,clear_workspace,List.length_nil,Nat.max_self] using trace
  | cons bit bits ih =>
    have trace := Execution.cons (clear_pop tape output work port bit bits) ih
    have first := mass_update work port (bit :: bits)
    have second := mass_update work port bits
    have peak : max (mass (Function.update work port (bit :: bits))) (mass (Function.update work port bits))=
        mass (Function.update work port (bit :: bits)) := by simp only [List.length_cons] at first; omega
    simpa only [clearProgram,clear_workspace,peak,List.length_cons,Nat.add_assoc] using trace

theorem clear_execution [Fintype K] [DecidableEq K] (port : K) (input : SpaceMachine.State K (Fin 2))
    (entry : input.pc=some (clearProgram port).main) :
    SpaceMachine.Execution (clearProgram port) input
      ⟨none,input.tape,Function.update input.work port [],input.output⟩ ((input.work port).length+2) (workspace input) := by
  have actual := clear_exact input.tape input.output input.work port (input.work port)
  have ready : clearState input.tape input.output input.work port (some (clearProgram port).main) (input.work port)=input := by
    cases input with
    | mk pc tape work output => cases entry; simp [clearState]
  rw [ready,Function.update_eq_self] at actual
  exact actual

abbrev CopyLabel := Fin 4 ⊕ Fin 6
def copyProgram (ports : Option Bool ↪ K) : SpaceMachine.Program K CopyLabel := SpaceWork.program ports StackCopy.program

def copyState [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (tape : ReadOnlyInput.Tape) (output : List Bool) (pc : Option CopyLabel) (source destination : List Bool) : SpaceMachine.State K CopyLabel :=
  SpaceWork.embedState ports frame tape output ⟨pc,StackBlocks.layout source destination []⟩

theorem copy_ready [DecidableEq K] (ports : Option Bool ↪ K) (input : SpaceMachine.State K CopyLabel)
    (clean : input.work (ports (some true))=[]) :
    copyState ports input.work input.tape input.output input.pc (input.work (ports none)) (input.work (ports (some false)))=input := by
  have bank : StackBlocks.layout (input.work (ports none)) (input.work (ports (some false))) []=
      (fun port => input.work (ports port)) := by
    funext port
    cases port with
    | none => rfl
    | some bit => cases bit <;> simp [StackBlocks.layout,clean]
  simp only [copyState,SpaceWork.embedState,bank,SpaceWork.ready_work]

theorem copied_work [DecidableEq K] (ports : Option Bool ↪ K) (frame : K → List Bool)
    (clean : frame (ports (some true))=[]) :
    SpaceWork.embedWork ports frame (StackBlocks.layout (frame (ports none)) (frame (ports none)++frame (ports (some false))) [])=
      Function.update frame (ports (some false)) (frame (ports none)++frame (ports (some false))) := by
  funext target
  by_cases mapped : ∃ port, target=ports port
  · obtain ⟨port,rfl⟩ := mapped
    rw [SpaceWork.embedWork_at]
    cases port with
    | none => simp [StackBlocks.layout,ports.injective.eq_iff]
    | some bit => cases bit <;> simp [StackBlocks.layout,ports.injective.eq_iff,clean]
  · have outside : ∀ port, target ≠ ports port := by simpa using mapped
    simp [SpaceWork.embedWork_other ports frame _ target outside,outside]

theorem copy_execution [Fintype K] [DecidableEq K] (ports : Option Bool ↪ K) (input : SpaceMachine.State K CopyLabel)
    (entry : input.pc=some (copyProgram ports).main) (clean : input.work (ports (some true))=[]) :
    ∃ peak, SpaceMachine.Execution (copyProgram ports) input
      ⟨none,input.tape,Function.update input.work (ports (some false))
        (input.work (ports none)++input.work (ports (some false))),input.output⟩
      (5*(input.work (ports none)).length+4) peak ∧ peak=workspace input+(input.work (ports none)).length := by
  have source := StackCopy.execution (input.work (ports none)) (input.work (ports (some false)))
  have compiled := SpaceWork.execution ports input.work input.tape input.output source
  have start : copyState ports input.work input.tape input.output (some StackCopy.program.main)
      (input.work (ports none)) (input.work (ports (some false)))=input := by
    change input.pc=some StackCopy.program.main at entry
    rw [← entry]
    exact copy_ready ports input clean
  change SpaceMachine.Execution (copyProgram ports)
    (copyState ports input.work input.tape input.output (some StackCopy.program.main)
      (input.work (ports none)) (input.work (ports (some false))))
    (copyState ports input.work input.tape input.output none (input.work (ports none))
      (input.work (ports none)++input.work (ports (some false)))) _ _ at compiled
  rw [start] at compiled
  have final : copyState ports input.work input.tape input.output none (input.work (ports none))
      (input.work (ports none)++input.work (ports (some false)))=
      ⟨none,input.tape,Function.update input.work (ports (some false))
        (input.work (ports none)++input.work (ports (some false))),input.output⟩ := by
    simp only [copyState,SpaceWork.embedState,copied_work ports input.work clean]
  rw [final] at compiled
  have mass := SpaceWork.workspace_embed ports input.work input.tape input.output
    (⟨some StackCopy.program.main,StackBlocks.layout (input.work (ports none)) (input.work (ports (some false))) []⟩ : StackMachine.State Bool CopyLabel)
  change workspace (copyState ports input.work input.tape input.output (some StackCopy.program.main)
    (input.work (ports none)) (input.work (ports (some false))))=_ at mass
  rw [start,StackBlocks.live_layout] at mass
  simp only [List.length_nil,Nat.add_zero] at mass
  exact ⟨_,compiled,by omega⟩

end Controller.Complexity.SpaceBuffers
