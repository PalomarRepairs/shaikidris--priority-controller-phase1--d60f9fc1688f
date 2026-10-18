module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.UnaryHalf
public import Controller.Complexity.GuardedLink

@[expose] public section

/-! A binary index is compared with a unary bound by successive halving.
The index and working bound are consumed; the shared stack returns an empty
success flag or `[false]`. Both work stacks are cleared on every input. -/
namespace Controller.Complexity.WordBound
open StackMachine StackBlocks
open scoped BigOperators

def halfPorts : Option Bool ↪ Option Bool :=
  StackFrames.threePorts (some false) (some true) none (by decide) (by decide) (by decide)

theorem halfPorts_apply (port : Option Bool) : halfPorts port =
    (match port with | none => some false | some false => some true | some true => none) := rfl

theorem half_storage (source destination word : List Bool) :
    StackFrames.embedStorage halfPorts (fun _ => []) (layout source destination word)=layout word source destination := by
  funext port
  cases port with
  | none => simp [StackFrames.embedStorage, halfPorts_apply, layout]
  | some bit => cases bit <;> simp [StackFrames.embedStorage, halfPorts_apply, layout]

theorem transfer_storage (word source destination : List Bool) :
    storage (layout word [] []) (some true) (some false) source destination=layout word destination source := by
  funext port
  cases port with
  | none => simp [storage, layout]
  | some bit => cases bit <;> simp [storage, layout]

def cycle (bit : Bool) := link (StackFrames.relocate halfPorts (UnaryHalf.program bit)) (transfer (some true) (some false))
abbrev BodyLabel := Fin 7 ⊕ Fin 4
abbrev Label := BodyLabel ⊕ Option (Fin 4)

theorem cycle_code (bit : Bool) : (cycle bit).code=(cycle false).code := rfl

theorem cycle_execution (bit : Bool) (bound : Nat) (word : List Bool) :
    ∃ peak, Execution (cycle bit) ⟨some (cycle bit).main,layout word (List.replicate bound true) []⟩
      ⟨none,layout word (List.replicate (UnaryHalf.shrink bit bound) true) []⟩
      (bound+3*UnaryHalf.shrink bit bound+4) peak := by
  obtain ⟨halfPeak,halving⟩ := UnaryHalf.execution bit bound [] word
  have lifted := StackFrames.execution halfPorts (fun _ => []) halving
  simp only [StackFrames.embedState, UnaryHalf.state, half_storage, List.append_nil] at lifted
  have moving := transfer_execution (layout word [] []) (source := some true) (destination := some false)
    (by decide) (List.replicate (UnaryHalf.shrink bit bound) true) []
  simp only [StackBlocks.state, transfer_storage, List.reverse_replicate, List.append_nil, List.length_replicate] at moving
  have trace := lifted.link moving
  have ticks : (bound+UnaryHalf.shrink bit bound+2)+(2*UnaryHalf.shrink bit bound+2)=bound+3*UnaryHalf.shrink bit bound+4 := by omega
  exact ⟨_,by simpa only [cycle, ticks] using trace⟩

def program : Program Bool Label where
  main := .inr (some 0)
  code label := match label with
    | .inl label => GuardedLink.leftInstruction none (0 : Fin 4) (fun _ => true) ((cycle false).code label)
    | .inr none => .halt
    | .inr (some position) => match position.val with
      | 0 => .pop none (.inr (some 1)) (.inl (cycle false).main) (.inl (cycle true).main)
      | 1 => .peek (some false) (.inr (some 2)) (.inr (some 3)) (.inr (some 3))
      | 2 => .push none false (.inr (some 3))
      | _ => .pop (some false) (.inr none) (.inr (some 3)) (.inr (some 3))

def state (label : Option Label) (word counter : List Bool) : State Bool Label := ⟨label,layout word counter []⟩

theorem body_step (bit : Bool) {current next : State Bool BodyLabel} (transition : step (cycle bit) current=some next) :
    step program (GuardedLink.leftState none (0 : Fin 4) (fun _ => true) current)=
      some (GuardedLink.leftState none (0 : Fin 4) (fun _ => true) next) := by
  cases position : current.pc with
  | none => simp [step, position] at transition
  | some label =>
    have next_eq : instructionStep ((cycle bit).code label) current=next := by simpa [step, position] using transition
    simp only [step, GuardedLink.leftState, position, Option.elim_some, Option.map_some, program]
    rw [← congrFun (cycle_code bit) label]
    exact congrArg some ((GuardedLink.leftInstruction_step none (0 : Fin 4) (fun _ => true) ((cycle bit).code label) current).trans
      (congrArg (GuardedLink.leftState none (0 : Fin 4) (fun _ => true)) next_eq))

theorem body_execution (bit : Bool) {current final : State Bool BodyLabel} {ticks peak}
    (trace : Execution (cycle bit) current final ticks peak) :
    Execution program (GuardedLink.leftState none (0 : Fin 4) (fun _ => true) current)
      (GuardedLink.leftState none (0 : Fin 4) (fun _ => true) final) ticks peak := by
  induction trace with
  | refl current => exact Execution.refl _
  | cons transition tail ih => exact Execution.cons (body_step bit transition) ih

theorem read_step (bit : Bool) (word : List Bool) (bound : Nat) :
    step program (state (some program.main) (bit :: word) (List.replicate bound true)) =
      some (GuardedLink.leftState none (0 : Fin 4) (fun _ => true)
        (⟨some (cycle bit).main,layout word (List.replicate bound true) []⟩ : State Bool BodyLabel)) := by
  cases bit <;> simp [step, program, state, instructionStep, layout, GuardedLink.leftState]
  all_goals funext port; cases port with
    | none => rfl
    | some value => cases value <;> rfl

theorem read_empty (bound : Nat) : step program (state (some program.main) [] (List.replicate bound true)) =
    some (state (some (.inr (some 1))) [] (List.replicate bound true)) := by
  simp [step, program, state, instructionStep, layout]

theorem test_empty : step program (state (some (.inr (some 1))) [] [])=some (state (some (.inr (some 2))) [] []) := rfl

theorem test_nonempty (counter : List Bool) : step program (state (some (.inr (some 1))) [] (true :: counter))=
    some (state (some (.inr (some 3))) [] (true :: counter)) := rfl

theorem set_error : step program (state (some (.inr (some 2))) [] [])=some (state (some (.inr (some 3))) [false] []) := by
  simp [step, program, state, instructionStep, layout]
  funext port
  cases port with
  | none => rfl
  | some value => cases value <;> rfl

theorem clear_pop (word counter : List Bool) :
    step program (state (some (.inr (some 3))) word (true :: counter))=
      some (state (some (.inr (some 3))) word counter) := by
  simp [step, program, state, instructionStep, layout]
  funext port
  cases port with
  | none => rfl
  | some value => cases value <;> rfl

theorem clear_empty (word : List Bool) : step program (state (some (.inr (some 3))) word [])=
    some (state (some (.inr none)) word []) := by simp [step, program, state, instructionStep, layout]

theorem halt_step (word : List Bool) : step program (state (some (.inr none)) word [])=some (state none word []) := rfl

theorem clear_execution (word : List Bool) (bound : Nat) :
    ∃ peak, Execution program (state (some (.inr (some 3))) word (List.replicate bound true))
      (state none word []) (bound+2) peak := by
  induction bound with
  | zero => exact ⟨_,Execution.cons (clear_empty word) (Execution.cons (halt_step word) (Execution.refl _))⟩
  | succ bound ih =>
    obtain ⟨peak,tail⟩ := ih
    exact ⟨_,by simpa only [List.replicate_succ, Nat.add_assoc] using Execution.cons (clear_pop word (List.replicate bound true)) tail⟩

theorem empty_execution (bound : Nat) :
    ∃ ticks peak, Execution program (state (some program.main) [] (List.replicate bound true))
      (state none (if 0 < bound then [] else [false]) []) ticks peak ∧ ticks ≤ bound+5 := by
  cases bound with
  | zero =>
    obtain ⟨peak,clearing⟩ := clear_execution [false] 0
    have trace := Execution.cons (read_empty 0) (Execution.cons test_empty (Execution.cons set_error clearing))
    exact ⟨5,_,by simpa using trace,le_rfl⟩
  | succ bound =>
    obtain ⟨peak,clearing⟩ := clear_execution [] (bound+1)
    have trace := Execution.cons (read_empty (bound+1)) (Execution.cons (test_nonempty (List.replicate bound true)) clearing)
    exact ⟨_,_,by simpa only [List.replicate_succ, Nat.zero_lt_succ, ite_true] using trace,by omega⟩

theorem execution (word : List Bool) (bound : Nat) :
    ∃ ticks peak, Execution program (state (some program.main) word (List.replicate bound true))
      (state none (if Encoding.value word < bound then [] else [false]) []) ticks peak ∧
      ticks ≤ word.length*(4*bound+5)+bound+5 := by
  induction word generalizing bound with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add]
    exact empty_execution bound
  | cons bit word ih =>
    let nextBound := UnaryHalf.shrink bit bound
    obtain ⟨tailTicks,tailPeak,tailRun,tailBound⟩ := ih nextBound
    obtain ⟨cyclePeak,cycleRun⟩ := cycle_execution bit bound word
    have lifted := body_execution bit cycleRun
    have boundary : GuardedLink.leftState none (0 : Fin 4) (fun _ => true)
        (⟨none,layout word (List.replicate nextBound true) []⟩ : State Bool BodyLabel)=
        state (some program.main) word (List.replicate nextBound true) := by
      simp [GuardedLink.leftState, GuardedLink.exitLabel, program, state]
    rw [boundary] at lifted
    have sameFlag : (if Encoding.value word < nextBound then [] else [false]) =
        (if Encoding.value (bit :: word) < bound then [] else [false]) := by
      have equivalence : Encoding.value (bit :: word) < bound ↔ Encoding.value word < nextBound := by
        simpa only [Encoding.value, nextBound] using UnaryHalf.comparison bit (Encoding.value word) bound
      by_cases smaller : Encoding.value word < nextBound
      · simp only [ite_eq_left smaller, ite_eq_left (equivalence.mpr smaller)]
      · have larger : ¬Encoding.value (bit :: word) < bound := fun h => smaller (equivalence.mp h)
        simp only [ite_eq_right smaller, ite_eq_right larger]
    rw [sameFlag] at tailRun
    have trace := Execution.cons (read_step bit word bound) (lifted.append tailRun)
    have shrinkBound := UnaryHalf.shrink_le bit bound
    have product := Nat.mul_le_mul_left word.length (show 4*nextBound+5 ≤ 4*bound+5 by dsimp [nextBound]; omega)
    refine ⟨(bound+3*nextBound+4)+tailTicks+1,_,trace,?_⟩
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 144 := by
  simpa [program, cycle, StackFrames.relocate, UnaryHalf.program, GuardedLink.leftInstruction, link] using finiteTM_resident program

end Controller.Complexity.WordBound
