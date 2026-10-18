module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceVirtualOrdinary
public import Controller.Complexity.SpaceVirtualLeft
public import Controller.Complexity.SpaceVirtualInput

@[expose] public section

/-! Every actual second-source instruction is simulated by a finite execution
of the fixed virtual-input program. The dirty first-machine workspace stays
bounded at returns; intermediate physical work is charged by the trace peak. -/
namespace Controller.Complexity.SpaceVirtualStep
open SpaceMachine SpaceVirtual

theorem execution [Fintype A] [Fintype B] [Fintype P] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) {function constant}
    (computes : LogSpaceBounds.Computes first function constant)
    (original : List Bool) (limit width : Nat) (shadow next : SpaceMachine.State B Q)
    (actual : SpaceMachine.State (Bank A B) (Label n P Q)) (related : Represents original shadow actual limit)
    (word : ReadOnlyInput.word shadow.tape=function original)
    (transition : SpaceMachine.step second shadow=some next)
    (counterWidth : SpaceLookupTrace.width (ReadOnlyInput.position shadow.tape) ≤ width)
    (nextWidth : (ReadOnlyInput.position next.tape).bits.length ≤ width)
    (budget : constant*LogSpaceBounds.bits original.length+width+1 ≤ limit) :
    ∃ result ticks peak, SpaceMachine.Execution (program first second enumeration) actual result ticks peak ∧
      Represents original next result limit ∧
      peak ≤ limit+max (workspace shadow) (workspace next)+width+1 := by
  obtain ⟨origin,position⟩ : ∃ origin, shadow.pc=some origin := by
    cases pc : shadow.pc with
    | none => simp [SpaceMachine.step,pc] at transition
    | some origin => exact ⟨origin,rfl⟩
  have nextEq : instructionStep (second.code origin) shadow=next := by
    simpa [SpaceMachine.step,position] using transition
  have size := SpaceLookupTrace.counter_length (ReadOnlyInput.position shadow.tape) (ReadOnlyInput.position shadow.tape) le_rfl
  have originalMass := related.toDataRep.workspace_le
  by_cases direct : SpaceVirtualOrdinary.ordinary (second.code origin)
  · obtain ⟨result,step,matched⟩ := SpaceVirtualOrdinary.simulation first second enumeration original limit shadow actual related origin position direct
    rw [nextEq] at matched
    have newMass := matched.toDataRep.workspace_le
    refine ⟨result,1,_,Execution.cons step (Execution.refl result),matched,?_⟩
    omega
  · cases code : second.code origin with
    | push port bit target => simp [code,SpaceVirtualOrdinary.ordinary] at direct
    | pop port empty low high => simp [code,SpaceVirtualOrdinary.ordinary] at direct
    | peek port empty low high => simp [code,SpaceVirtualOrdinary.ordinary] at direct
    | readInput eof low high =>
      obtain ⟨result,ticks,peak,trace,matched,space⟩ := SpaceVirtualInput.read first second enumeration computes
        original limit width shadow actual related word origin eof low high position code counterWidth budget
      have same : instructionStep (.readInput eof low high) shadow=next := by simpa only [code] using nextEq
      rw [same] at matched
      exact ⟨result,ticks,peak,trace,matched,by omega⟩
    | atStart yes no => simp [code,SpaceVirtualOrdinary.ordinary] at direct
    | left target =>
      obtain ⟨result,ticks,trace,matched⟩ := SpaceVirtualLeft.execution first second enumeration original limit shadow actual related origin target position code
      have same : instructionStep (.left target) shadow=next := by simpa only [code] using nextEq
      rw [same] at matched
      exact ⟨result,ticks,_,trace,matched,by omega⟩
    | right target =>
      obtain ⟨result,ticks,peak,trace,matched,space⟩ := SpaceVirtualInput.right first second enumeration computes
        original limit width shadow actual related word origin target position code counterWidth budget
      have same : instructionStep (.right target) shadow=next := by simpa only [code] using nextEq
      rw [same] at matched
      exact ⟨result,ticks,peak,trace,matched,by omega⟩
    | emit bit target => simp [code,SpaceVirtualOrdinary.ordinary] at direct
    | jump target => simp [code,SpaceVirtualOrdinary.ordinary] at direct
    | halt => simp [code,SpaceVirtualOrdinary.ordinary] at direct

end Controller.Complexity.SpaceVirtualStep
