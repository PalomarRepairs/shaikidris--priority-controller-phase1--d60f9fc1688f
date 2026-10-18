module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceVirtualStep

@[expose] public section

/-! Complete finite second-source executions run on the fixed virtual-input
program. Source traces establish termination; actual workspace includes the
first transducer, retained second work and both binary-head counter copies. -/
namespace Controller.Complexity.SpaceVirtualRun
open SpaceMachine SpaceVirtual

theorem head_width (tape : ReadOnlyInput.Tape) :
    SpaceLookupTrace.width (ReadOnlyInput.position tape) ≤ SpaceLookupTrace.width (ReadOnlyInput.word tape).length := by
  have position := ReadOnlyInput.position_le tape
  have logarithm := Nat.log_mono_right (b:=2)
    (show ReadOnlyInput.position tape+2 ≤ (ReadOnlyInput.word tape).length+2 by omega)
  dsimp only [SpaceLookupTrace.width]
  omega

theorem head_length (tape : ReadOnlyInput.Tape) :
    (ReadOnlyInput.position tape).bits.length ≤ SpaceLookupTrace.width (ReadOnlyInput.word tape).length :=
  (SpaceLookupTrace.counter_length _ _ le_rfl).trans (head_width tape)

theorem execution [Fintype A] [Fintype B] [Fintype P] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) {function constant}
    (computes : LogSpaceBounds.Computes first function constant)
    (original : List Bool) (limit : Nat) {shadow final sourceTicks sourcePeak}
    (trace : SpaceMachine.Execution second shadow final sourceTicks sourcePeak)
    (actual : SpaceMachine.State (Bank A B) (Label n P Q)) (related : Represents original shadow actual limit)
    (word : ReadOnlyInput.word shadow.tape=function original)
    (budget : constant*LogSpaceBounds.bits original.length+SpaceLookupTrace.width (function original).length+1 ≤ limit) :
    ∃ result ticks peak, SpaceMachine.Execution (program first second enumeration) actual result ticks peak ∧
      Represents original final result limit ∧
      peak ≤ limit+sourcePeak+SpaceLookupTrace.width (function original).length+1 := by
  induction trace generalizing actual with
  | refl shadow =>
    have size := head_length shadow.tape
    rw [word] at size
    have mass := related.toDataRep.workspace_le
    exact ⟨actual,0,_,Execution.refl _,related,by omega⟩
  | @cons shadow next final sourceTicks sourcePeak transition rest ih =>
    have nextWord : ReadOnlyInput.word next.tape=function original := (SpaceMachine.step_word transition).trans word
    have width := head_width shadow.tape
    rw [word] at width
    have nextLength := head_length next.tape
    rw [nextWord] at nextLength
    obtain ⟨middle,firstTicks,firstPeak,firstTrace,matched,firstSpace⟩ := SpaceVirtualStep.execution first second enumeration computes
      original limit (SpaceLookupTrace.width (function original).length) shadow next actual related word transition width nextLength budget
    obtain ⟨result,ticks,peak,tail,finalMatched,tailSpace⟩ := ih middle matched nextWord
    have complete := firstTrace.append tail
    have nextMass := rest.initial_workspace_le
    exact ⟨result,_,_,complete,finalMatched,by omega⟩

theorem cold [Fintype A] [Fintype B] [Fintype P] [DecidableEq A] [DecidableEq B]
    (first : SpaceMachine.Program A P) (second : SpaceMachine.Program B Q)
    (enumeration : Fin n ≃ SpaceLookup.Bank A) {function target firstConstant secondConstant}
    (firstComputes : LogSpaceBounds.Computes first function firstConstant)
    (secondComputes : LogSpaceBounds.Computes second target secondConstant) (input : List Bool) :
    ∃ result ticks peak, SpaceMachine.Execution (program first second enumeration)
      (SpaceMachine.initial (program first second enumeration) input) result ticks peak ∧
      result.pc=none ∧ result.output.reverse=target (function input) ∧
      peak ≤ firstConstant*LogSpaceBounds.bits input.length+
        (secondConstant+2)*LogSpaceBounds.bits (function input).length+2 := by
  obtain ⟨final,sourceTicks,sourcePeak,trace,stopped,output,space⟩ := secondComputes.2 (function input)
  let width := SpaceLookupTrace.width (function input).length
  let limit := firstConstant*LogSpaceBounds.bits input.length+width+1
  have initial := SpaceVirtual.initial first second enumeration input (function input) limit
  obtain ⟨result,ticks,peak,actual,matched,peakBound⟩ := execution first second enumeration firstComputes input limit trace
    (SpaceMachine.initial (program first second enumeration) input) initial (ReadOnlyInput.word_start _) le_rfl
  refine ⟨result,ticks,peak,actual,?_,?_,?_⟩
  · simpa only [stopped,Option.map_none] using matched.pc
  · rw [matched.output,output]
  · change peak ≤ firstConstant*LogSpaceBounds.bits input.length+width+1+sourcePeak+width+1 at peakBound
    change sourcePeak ≤ secondConstant*width at space
    change peak ≤ firstConstant*LogSpaceBounds.bits input.length+(secondConstant+2)*width+2
    simp only [Nat.add_mul,Nat.two_mul]
    omega

end Controller.Complexity.SpaceVirtualRun
