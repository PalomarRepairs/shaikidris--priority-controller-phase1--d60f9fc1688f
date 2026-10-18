module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceLookup
public import Controller.Complexity.SpaceEmissions

@[expose] public section

/-! Every requested intermediate bit is recomputed by the fixed interception
program from a finite halted source trace. The physical run either returns
that bit in its answer bank or the empty EOF answer. Its workspace includes
the source peak, a logarithmic binary countdown and one answer bit. -/
namespace Controller.Complexity.SpaceLookupTrace
open SpaceMachine

def width (limit : Nat) := Nat.log 2 (limit+2)+1
def budget (limit : Nat) := 4*width limit+5

theorem counter_length (number limit : Nat) (bound : number ≤ limit) : number.bits.length ≤ width limit := by
  have size := BinaryIncrement.counter_length number
  have monotone := Nat.log_mono_right (b:=2) (show number+2 ≤ limit+2 by omega)
  dsimp only [width]
  omega

theorem execution [Fintype K] [DecidableEq K] {source : SpaceMachine.Program K Q}
    {input final ticks peak stream} (trace : SpaceEmissions.Trace source input final ticks peak stream)
    (halted : final.pc=none) (output : List Bool) (number limit : Nat) (bound : number ≤ limit) :
    ∃ result actualTicks actualPeak,
      SpaceMachine.Execution (SpaceLookup.program source) (SpaceLookup.view output input number) result actualTicks actualPeak ∧
      result.pc=none ∧ result.output=output ∧ result.work SpaceLookup.answer=(stream[number]?).toList ∧
      actualTicks ≤ ticks*budget limit+3 ∧ actualPeak ≤ peak+width limit+1 := by
  induction trace generalizing number with
  | refl input =>
    refine ⟨SpaceLookup.view output input number,0,_,Execution.refl _,?_,rfl,?_,by omega,?_⟩
    · simp [SpaceLookup.view,SpaceControl.state,SpaceSuppress.state,halted]
    · simp [SpaceLookup.view,SpaceControl.state,SpaceSuppress.state,SpaceLookup.frame,SpaceLookup.answer]
    · rw [SpaceLookup.workspace_view]
      have size := counter_length number limit bound
      omega
  | @cons input next final ticks peak stream actual rest ih =>
    obtain ⟨label,position⟩ : ∃ label, input.pc=some label := by
      cases pc : input.pc with
      | none => simp [SpaceMachine.step,pc] at actual
      | some label => exact ⟨label,rfl⟩
    have nextEq : instructionStep (source.code label) input=next := by
      simpa [SpaceMachine.step,position] using actual
    by_cases ordinary : emitted (source.code label)=none
    · obtain ⟨result,time,space,tail,stopped,retained,answer,timeBound,spaceBound⟩ := ih halted number bound
      have first := SpaceLookup.ordinary_step source output input label number position ordinary
      rw [nextEq] at first
      have complete := Execution.cons first tail
      refine ⟨result,time+1,_,complete,stopped,retained,?_,?_,?_⟩
      · simpa [SpaceEmissions.event,position,ordinary] using answer
      · have positive : 1 ≤ budget limit := by simp [budget]
        rw [Nat.add_mul,Nat.one_mul]
        omega
      · have size := counter_length number limit bound
        simp only [SpaceLookup.workspace_view]
        omega
    · obtain ⟨bit,target,code⟩ : ∃ bit target, source.code label=.emit bit target := by
        cases code : source.code label <;> simp_all [emitted]
      have shape : next=instructionStep (.emit bit target) input := by rw [← nextEq,code]
      cases number with
      | zero =>
        have complete := SpaceLookup.capture_execution source output input label target bit position code
        refine ⟨_,3,_,complete,rfl,rfl,?_,by omega,?_⟩
        · simp [SpaceEmissions.event,position,code,emitted,SpaceLookup.work,SpaceLookup.frame,SpaceLookup.answer]
        · omega
      | succ number =>
        obtain ⟨result,time,space,tail,stopped,retained,answer,timeBound,spaceBound⟩ :=
          ih halted number (by omega)
        have skipped := SpaceLookup.skip_execution source output input label target bit number position code
        have same : SpaceLookup.view output { input with pc := some target } number=SpaceLookup.view output next number := by
          rw [shape]
          rfl
        rw [same] at skipped
        have complete := skipped.append tail
        refine ⟨result,_,_,complete,stopped,retained,?_,?_,?_⟩
        · simpa [SpaceEmissions.event,position,code,emitted] using answer
        · have cost := BinaryDecrement.cost_le (number+1).bits
          have size := counter_length (number+1) limit bound
          dsimp only [budget] at timeBound ⊢
          rw [Nat.add_mul,Nat.one_mul]
          omega
        · have size := counter_length (number+1) limit bound
          omega

theorem from_execution [Fintype K] [DecidableEq K] {source : SpaceMachine.Program K Q}
    {input final ticks peak} (trace : SpaceMachine.Execution source input final ticks peak)
    (halted : final.pc=none) (output : List Bool) (number : Nat) :
    ∃ result actualTicks actualPeak,
      SpaceMachine.Execution (SpaceLookup.program source) (SpaceLookup.view output input number) result actualTicks actualPeak ∧
      result.pc=none ∧ result.output=output ∧
      result.work SpaceLookup.answer=((final.output.reverse.drop input.output.length)[number]?).toList ∧
      actualTicks ≤ ticks*budget number+3 ∧ actualPeak ≤ peak+width number+1 := by
  obtain ⟨stream,emissions⟩ := SpaceEmissions.of_execution trace
  have lookup := execution emissions halted output number number le_rfl
  rwa [SpaceEmissions.stream_eq emissions] at lookup

end Controller.Complexity.SpaceLookupTrace
