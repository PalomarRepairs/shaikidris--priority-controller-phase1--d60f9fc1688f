module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceVirtualQuery
public import Controller.Complexity.SpaceVirtualCounter
public import Controller.Complexity.SpaceVirtualState

@[expose] public section

/-! Virtual input operations use actual first-output requests. The invariant
bounds dirty first-machine work uniformly across repeated requests and retains
the entire second-machine caller state. -/
namespace Controller.Complexity.SpaceVirtualInput
open SpaceMachine SpaceVirtual SpaceVirtualState

theorem query [Fintype A] [Fintype B] [Fintype P] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) {function constant}
    (computes : LogSpaceBounds.Computes first function constant)
    (original : List Bool) (limit width : Nat) (shadow : SpaceMachine.State B Q)
    (actual : SpaceMachine.State (Bank A B) (Label n P Q)) (related : DataRep original shadow actual limit)
    (word : ReadOnlyInput.word shadow.tape=function original) (origin : Q)
    (counterWidth : SpaceLookupTrace.width (ReadOnlyInput.position shadow.tape) ≤ width)
    (budget : constant*LogSpaceBounds.bits original.length+width+1 ≤ limit) :
    ∃ middle ticks peak, SpaceMachine.Execution (program first second enumeration)
      { actual with pc := some (requestLabel origin (SpaceRequest.program first enumeration (headCaller (B:=B))).main) }
      middle ticks peak ∧ middle.pc=some (finishLabel origin) ∧
      DataRep original shadow middle limit ∧ (middle.work answerPort).head?=ReadOnlyInput.symbol shadow.tape ∧
      peak ≤ limit+workspace shadow+width := by
  obtain ⟨middle,ticks,peak,trace,position,output,input,answer,caller,left,space⟩ :=
    SpaceVirtualQuery.execution first second enumeration computes actual origin
      (ReadOnlyInput.position shadow.tape) related.head
  rw [related.input] at answer left space
  have bounded : leftMass middle ≤ limit := by have old := related.left; omega
  have data := retain related input output caller bounded
  have symbol : ReadOnlyInput.symbol shadow.tape=(function original)[ReadOnlyInput.position shadow.tape]? := by
    rw [ReadOnlyInput.symbol_eq,word]
  have head : (middle.work answerPort).head?=ReadOnlyInput.symbol shadow.tape := by
    rw [answer,← symbol]
    cases ReadOnlyInput.symbol shadow.tape <;> rfl
  have size := SpaceLookupTrace.counter_length (ReadOnlyInput.position shadow.tape) (ReadOnlyInput.position shadow.tape) le_rfl
  have originalMass := related.workspace_le
  have frame := related.caller_mass
  refine ⟨middle,ticks,peak,trace,position,data,head,?_⟩
  omega

theorem read [Fintype A] [Fintype B] [Fintype P] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) {function constant}
    (computes : LogSpaceBounds.Computes first function constant)
    (original : List Bool) (limit width : Nat) (shadow : SpaceMachine.State B Q)
    (actual : SpaceMachine.State (Bank A B) (Label n P Q)) (related : Represents original shadow actual limit)
    (word : ReadOnlyInput.word shadow.tape=function original) (origin eof low high : Q)
    (position : shadow.pc=some origin) (code : second.code origin=.readInput eof low high)
    (counterWidth : SpaceLookupTrace.width (ReadOnlyInput.position shadow.tape) ≤ width)
    (budget : constant*LogSpaceBounds.bits original.length+width+1 ≤ limit) :
    ∃ result ticks peak, SpaceMachine.Execution (program first second enumeration) actual result ticks peak ∧
      Represents original (instructionStep (.readInput eof low high) shadow) result limit ∧
      peak ≤ limit+workspace shadow+width := by
  have firstStep : SpaceMachine.step (program first second enumeration) actual=
      some { actual with pc := some (requestLabel origin (SpaceRequest.program first enumeration (headCaller (B:=B))).main) } := by
    simp [SpaceMachine.step,related.pc,position,program,sourceLabel,code,instructionStep,advance]
  obtain ⟨middle,ticks,peak,trace,atFinish,data,answer,space⟩ :=
    query first second enumeration computes original limit width shadow actual related.toDataRep word origin counterWidth budget
  let result : SpaceMachine.State (Bank A B) (Label n P Q) :=
    { middle with pc := some (sourceLabel (observed eof low high (ReadOnlyInput.symbol shadow.tape))) }
  have lastStep : SpaceMachine.step (program first second enumeration) middle=some result := by
    simp only [SpaceMachine.step,atFinish,Option.map_some,program,finishLabel,code,instructionStep,advance,
      answer,SpaceControl.observed_map,result]
  have last := Execution.cons lastStep (Execution.refl result)
  have complete := (Execution.cons firstStep trace).append last
  have finalData : DataRep original (instructionStep (.readInput eof low high) shadow) result limit :=
    shadow_change (after:=instructionStep (.readInput eof low high) shadow)
      (retain (after:=result) data rfl rfl (fun _ => rfl) data.left) rfl rfl rfl
  have initialMass := trace.initial_workspace_le
  have finalMass := trace.final_workspace_le
  have resultMass : workspace result=workspace middle := rfl
  refine ⟨result,_,_,complete,⟨finalData,rfl⟩,?_⟩
  change workspace actual ≤ peak at initialMass
  omega

theorem position_right_none (tape : ReadOnlyInput.Tape) (empty : ReadOnlyInput.symbol tape=none) :
    ReadOnlyInput.position (ReadOnlyInput.moveRight tape)=ReadOnlyInput.position tape := by
  cases right : tape.right <;> simp_all [ReadOnlyInput.symbol,ReadOnlyInput.position,ReadOnlyInput.moveRight]

theorem position_right_some (tape : ReadOnlyInput.Tape) (bit : Bool) (present : ReadOnlyInput.symbol tape=some bit) :
    ReadOnlyInput.position (ReadOnlyInput.moveRight tape)=ReadOnlyInput.position tape+1 := by
  cases right : tape.right <;> simp_all [ReadOnlyInput.symbol,ReadOnlyInput.position,ReadOnlyInput.moveRight]

theorem right [Fintype A] [Fintype B] [Fintype P] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) {function constant}
    (computes : LogSpaceBounds.Computes first function constant)
    (original : List Bool) (limit width : Nat) (shadow : SpaceMachine.State B Q)
    (actual : SpaceMachine.State (Bank A B) (Label n P Q)) (related : Represents original shadow actual limit)
    (word : ReadOnlyInput.word shadow.tape=function original) (origin next : Q)
    (position : shadow.pc=some origin) (code : second.code origin=.right next)
    (counterWidth : SpaceLookupTrace.width (ReadOnlyInput.position shadow.tape) ≤ width)
    (budget : constant*LogSpaceBounds.bits original.length+width+1 ≤ limit) :
    ∃ result ticks peak, SpaceMachine.Execution (program first second enumeration) actual result ticks peak ∧
      Represents original (instructionStep (.right next) shadow) result limit ∧
      peak ≤ limit+workspace shadow+width+1 := by
  have firstStep : SpaceMachine.step (program first second enumeration) actual=
      some { actual with pc := some (requestLabel origin (SpaceRequest.program first enumeration (headCaller (B:=B))).main) } := by
    simp [SpaceMachine.step,related.pc,position,program,sourceLabel,code,instructionStep,advance]
  obtain ⟨middle,ticks,peak,trace,atFinish,data,answer,space⟩ :=
    query first second enumeration computes original limit width shadow actual related.toDataRep word origin counterWidth budget
  have initialMass := trace.initial_workspace_le
  have finalMass := trace.final_workspace_le
  change workspace actual ≤ peak at initialMass
  cases symbol : ReadOnlyInput.symbol shadow.tape with
  | none =>
    let result : SpaceMachine.State (Bank A B) (Label n P Q) := { middle with pc := some (sourceLabel next) }
    have lastStep : SpaceMachine.step (program first second enumeration) middle=some result := by
      simp only [SpaceMachine.step,atFinish,Option.map_some,program,finishLabel,code,instructionStep,advance,
        answer,symbol,observed,result]
    have complete := (Execution.cons firstStep trace).append (Execution.cons lastStep (Execution.refl result))
    have finalData : DataRep original (instructionStep (.right next) shadow) result limit :=
      shadow_change (after:=instructionStep (.right next) shadow)
        (retain (after:=result) data rfl rfl (fun _ => rfl) data.left) rfl (position_right_none shadow.tape symbol) rfl
    have resultMass : workspace result=workspace middle := rfl
    refine ⟨result,_,_,complete,⟨finalData,rfl⟩,?_⟩
    omega
  | some bit =>
    have lastStep : SpaceMachine.step (program first second enumeration) middle=
        some ⟨some (incrementLabel next (SpaceCounter.program (ports (A:=A) (B:=B))).main),middle.tape,middle.work,middle.output⟩ := by
      cases bit <;>
        simp only [SpaceMachine.step,atFinish,Option.map_some,program,finishLabel,code,instructionStep,advance,
          answer,symbol,observed]
    obtain ⟨counterTicks,counterPeak,counterTrace,counterSpace⟩ := SpaceVirtualCounter.increment first second enumeration middle next
      (ReadOnlyInput.position shadow.tape) data.head data.scratch
    have complete := (Execution.cons firstStep trace).append (Execution.cons lastStep counterTrace)
    let result : SpaceMachine.State (Bank A B) (Label n P Q) :=
      ⟨some (sourceLabel next),middle.tape,
        Function.update middle.work headPort (ReadOnlyInput.position shadow.tape+1).bits,middle.output⟩
    have finalData : DataRep original (instructionStep (.right next) shadow) result limit :=
      head_change (after:=instructionStep (.right next) shadow) data rfl (position_right_some shadow.tape bit symbol) rfl _
    refine ⟨result,_,_,complete,⟨finalData,rfl⟩,?_⟩
    omega

end Controller.Complexity.SpaceVirtualInput
