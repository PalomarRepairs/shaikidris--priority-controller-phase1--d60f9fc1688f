module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceVirtual

@[expose] public section

/-! First-output requests inside the actual second-machine simulator.
The entire caller state is preserved, and the dirty first-machine workspace
is bounded independently of the number of preceding requests. -/
namespace Controller.Complexity.SpaceVirtualQuery
open SpaceMachine SpaceVirtual

theorem execution [Fintype A] [Fintype B] [Fintype P] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) {function constant}
    (computes : LogSpaceBounds.Computes first function constant)
    (state : SpaceMachine.State (Bank A B) (Label n P Q)) (origin : Q) (number : Nat)
    (encoded : state.work headPort=number.bits) :
    ∃ result ticks peak, SpaceMachine.Execution (program first second enumeration)
      { state with pc := some (requestLabel origin (SpaceRequest.program first enumeration (headCaller (B:=B))).main) }
      result ticks peak ∧
      result.pc=some (finishLabel origin) ∧ result.output=state.output ∧
      ReadOnlyInput.word result.tape=ReadOnlyInput.word state.tape ∧
      result.work answerPort=((function (ReadOnlyInput.word state.tape))[number]?).toList ∧
      (∀ port, result.work (.inr port)=state.work (.inr port)) ∧
      leftMass result ≤ max (leftMass state)
        (constant*LogSpaceBounds.bits (ReadOnlyInput.word state.tape).length+SpaceLookupTrace.width number+1) ∧
      peak ≤ max (workspace state)
        (callerMass state+constant*LogSpaceBounds.bits (ReadOnlyInput.word state.tape).length+SpaceLookupTrace.width number+1) := by
  let input : SpaceMachine.State (Bank A B) (SpaceRequest.Label n P) :=
    ⟨some (SpaceRequest.program first enumeration (headCaller (B:=B))).main,state.tape,state.work,state.output⟩
  obtain ⟨found,ticks,peak,actual,stopped,output,answer,caller,time,space⟩ :=
    SpaceRequest.computed first enumeration headCaller computes input rfl number encoded
  have compiled := SpaceControl.execution (SpaceRequest.program first enumeration (headCaller (B:=B)))
    (program first second enumeration) (requestLabel origin) (some (finishLabel origin)) (fun _ => rfl) actual
  let result : SpaceMachine.State (Bank A B) (Label n P Q) :=
    ⟨some (finishLabel origin),found.tape,found.work,found.output⟩
  have finalEq : SpaceControl.state (requestLabel origin) (some (finishLabel origin)) found=result := by
    simp only [SpaceControl.state,stopped,Option.elim_none,result]
  have initialEq : SpaceControl.state (requestLabel origin) (some (finishLabel origin)) input=
      { state with pc := some (requestLabel origin (SpaceRequest.program first enumeration (headCaller (B:=B))).main) } := rfl
  rw [initialEq,finalEq] at compiled
  change peak ≤ max (workspace state)
    (callerMass state+constant*LogSpaceBounds.bits (ReadOnlyInput.word state.tape).length+SpaceLookupTrace.width number+1) at space
  have callerEq : callerMass result=callerMass state := by
    unfold callerMass SpaceBuffers.mass
    apply Finset.sum_congr rfl
    intro port _
    exact congrArg List.length (caller port)
  have finalBound := compiled.final_workspace_le
  rw [workspace_split,callerEq] at finalBound
  have initialMass := workspace_split state
  refine ⟨result,ticks,peak,compiled,rfl,output,compiled.input_preserved,answer,caller,?_,space⟩
  omega

end Controller.Complexity.SpaceVirtualQuery
