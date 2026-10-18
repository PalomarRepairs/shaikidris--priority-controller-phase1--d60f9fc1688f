module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.StackFrames

@[expose] public section

/-! A fixed finite routine duplicates a bit stack while preserving its source.
The destination may contain an existing suffix; the scratch stack starts and
ends empty. The routine can be relocated into an arbitrary surrounding frame. -/
namespace Controller.Complexity.StackCopy
open StackMachine StackBlocks
open scoped BigOperators

def forkProgram : Program Bool (Fin 6) where
  main := 0
  code label := match label.val with
    | 0 => .pop (some true) 5 1 2
    | 1 => .push none false 3
    | 2 => .push none true 4
    | 3 => .push (some false) false 0
    | 4 => .push (some false) true 0
    | _ => .halt

def forkState (label : Option (Fin 6)) (shared destination scratch : List Bool) : State Bool (Fin 6) :=
  ⟨label, layout shared destination scratch⟩

def firstLabel (bit : Bool) : Fin 6 := if bit then 2 else 1
def secondLabel (bit : Bool) : Fin 6 := if bit then 4 else 3

theorem pop_step (bit : Bool) (input shared destination : List Bool) :
    step forkProgram (forkState (some 0) shared destination (bit :: input)) =
      some (forkState (some (firstLabel bit)) shared destination input) := by
  cases bit <;> simp [step, forkProgram, forkState, firstLabel, instructionStep, layout]
  all_goals funext stack; cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl

theorem push_shared (bit : Bool) (input shared destination : List Bool) :
    step forkProgram (forkState (some (firstLabel bit)) shared destination input) =
      some (forkState (some (secondLabel bit)) (bit :: shared) destination input) := by
  cases bit <;> simp [step, forkProgram, forkState, firstLabel, secondLabel, instructionStep, layout]
  all_goals funext stack; cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl

theorem push_destination (bit : Bool) (input shared destination : List Bool) :
    step forkProgram (forkState (some (secondLabel bit)) (bit :: shared) destination input) =
      some (forkState (some 0) (bit :: shared) (bit :: destination) input) := by
  cases bit <;> simp [step, forkProgram, forkState, secondLabel, instructionStep, layout]
  all_goals funext stack; cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl

theorem empty_step (shared destination : List Bool) :
    step forkProgram (forkState (some 0) shared destination []) =
      some (forkState (some 5) shared destination []) := by
  simp [step, forkProgram, forkState, instructionStep, layout]

theorem halt_step (shared destination : List Bool) :
    step forkProgram (forkState (some 5) shared destination []) =
      some (forkState none shared destination []) := rfl

theorem fork_execution (input shared destination : List Bool) :
    Execution forkProgram (forkState (some 0) shared destination input)
      (forkState none (input.reverse ++ shared) (input.reverse ++ destination) [])
      (3*input.length+2) (2*input.length+shared.length+destination.length) := by
  induction input generalizing shared destination with
  | nil =>
    have done := Execution.refl (program := forkProgram) (forkState none shared destination [])
    have trace := Execution.cons (empty_step shared destination) (Execution.cons (halt_step shared destination) done)
    simpa [forkState, live_layout] using trace
  | cons bit input ih =>
    have tail := ih (bit :: shared) (bit :: destination)
    have one := Execution.cons (push_destination bit input shared destination) tail
    have two := Execution.cons (push_shared bit input shared destination) one
    have three := Execution.cons (pop_step bit input shared destination) two
    have count : ((3*input.length+2)+1)+1+1 = 3*(bit :: input).length+2 := by
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [count] at three
    have peak : max (live (forkState (some 0) shared destination (bit :: input)))
        (max (live (forkState (some (firstLabel bit)) shared destination input))
          (max (live (forkState (some (secondLabel bit)) (bit :: shared) destination input))
            (2*input.length+(bit :: shared).length+(bit :: destination).length))) =
        2*(bit :: input).length+shared.length+destination.length := by
      simp only [forkState, live_layout, List.length_cons]
      omega
    rw [peak] at three
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using three

theorem transfer_layout (input destination scratch : List Bool) :
    storage (layout [] destination []) none (some true) input scratch = layout input destination scratch := by
  funext stack
  cases stack with
  | none => simp [storage, layout]
  | some bit => cases bit <;> simp [storage, layout]

def program := link (transfer (K := Bool) none (some true)) forkProgram

theorem execution (input destination : List Bool) :
    Execution program ⟨some program.main, layout input destination []⟩
      ⟨none, layout input (input ++ destination) []⟩
      (5*input.length+4) (2*input.length+destination.length) := by
  have first := transfer_execution (layout [] destination [])
    (source := none) (destination := some true) (by decide) input []
  simp only [StackBlocks.state, List.append_nil, transfer_layout, live_layout, List.length_nil, Nat.add_zero] at first
  have second := fork_execution input.reverse [] destination
  simp only [forkState, List.reverse_reverse, List.append_nil, List.length_reverse, List.length_nil, Nat.add_zero] at second
  have trace := first.link second
  have count : (2*input.length+2)+(3*input.length+2)=5*input.length+4 := by omega
  rw [count] at trace
  have peak : max (input.length+destination.length) (2*input.length+destination.length) =
      2*input.length+destination.length := by omega
  simpa only [program, peak] using trace

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 90 := by
  simpa [program] using finiteTM_resident program

theorem framed_execution [Fintype K] [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (input destination : List Bool) :
    Execution (StackFrames.relocate ports program)
      (StackFrames.embedState ports frame (⟨some program.main, layout input destination []⟩ : State Bool _))
      (StackFrames.embedState ports frame (⟨none, layout input (input ++ destination) []⟩ : State Bool _))
      (5*input.length+4) (2*input.length+destination.length+StackFrames.frameBits ports frame) :=
  StackFrames.execution ports frame (execution input destination)

theorem ready_storage [DecidableEq K] (ports : Option Bool ↪ Option K) (frame : Option K → List Bool)
    (clean : frame (ports (some true))=[]) :
    StackFrames.embedStorage ports frame (layout (frame (ports none)) (frame (ports (some false))) [])=frame := by
  funext target
  by_cases mapped : ∃ port, target=ports port
  · obtain ⟨port,rfl⟩ := mapped
    rw [StackFrames.embedStorage_at]
    cases port with
    | none => rfl
    | some bit => cases bit with
      | false => rfl
      | true => exact clean.symm
  · exact StackFrames.embedStorage_other ports frame _ target (by simpa using mapped)

theorem ready_execution [Fintype K] [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (clean : frame (ports (some true))=[]) :
    ∃ peak, Execution (StackFrames.relocate ports program)
      ⟨some program.main,frame⟩
      ⟨none,Function.update frame (ports (some false)) (frame (ports none)++frame (ports (some false)))⟩
      (5*(frame (ports none)).length+4) peak := by
  have trace := framed_execution ports frame (frame (ports none)) (frame (ports (some false)))
  have updated : layout (frame (ports none)) (frame (ports none)++frame (ports (some false))) []=
      Function.update (layout (frame (ports none)) (frame (ports (some false))) []) (some false)
        (frame (ports none)++frame (ports (some false))) := by
    funext port
    cases port with
    | none => simp [layout]
    | some bit => cases bit <;> simp [layout]
  exact ⟨_,by simpa only [StackFrames.embedState, updated, StackFrames.embedStorage_update,
    ready_storage ports frame clean] using trace⟩

end Controller.Complexity.StackCopy
