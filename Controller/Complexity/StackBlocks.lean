module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.Reductions

@[expose] public section

/-! Finite-control stack movement blocks preserve all unselected stacks.
These blocks operate on existing work data and use shared-stack linking. -/
namespace Controller.Complexity.StackBlocks
open StackMachine
open scoped BigOperators

def storage [DecidableEq K] (base : Option K → List Bool) (source destination : Option K)
    (input output : List Bool) : Option K → List Bool :=
  Function.update (Function.update base source input) destination output

def state [DecidableEq K] (label : Option (Fin 4)) (base : Option K → List Bool)
    (source destination : Option K) (input output : List Bool) : State K (Fin 4) :=
  ⟨label, storage base source destination input output⟩

theorem storage_source [DecidableEq K] (base : Option K → List Bool) {source destination : Option K}
    (distinct : source ≠ destination) (input output : List Bool) :
    storage base source destination input output source = input := by
  simp [storage, Function.update_of_ne distinct]

theorem storage_destination [DecidableEq K] (base : Option K → List Bool) (source destination : Option K)
    (input output : List Bool) : storage base source destination input output destination = output := by
  simp [storage]

theorem storage_other [DecidableEq K] (base : Option K → List Bool) (source destination : Option K)
    (input output : List Bool) {target : Option K} (notSource : target ≠ source) (notDestination : target ≠ destination) :
    storage base source destination input output target = base target := by
  simp [storage, Function.update_of_ne notSource, Function.update_of_ne notDestination]

theorem update_source [DecidableEq K] (base : Option K → List Bool) {source destination : Option K}
    (distinct : source ≠ destination) (input output replacement : List Bool) :
    Function.update (storage base source destination input output) source replacement =
      storage base source destination replacement output := by
  funext target
  by_cases hs : target=source <;> by_cases hd : target=destination <;>
    simp_all [storage, Function.update_apply]

theorem update_destination [DecidableEq K] (base : Option K → List Bool) (source destination : Option K)
    (input output replacement : List Bool) :
    Function.update (storage base source destination input output) destination replacement =
      storage base source destination input replacement := by
  funext target
  by_cases hd : target=destination <;> simp [storage, Function.update_apply, hd]

def transfer (source destination : Option K) : Program K (Fin 4) where
  main := 0
  code label := match label.val with
    | 0 => .pop source 3 1 2
    | 1 => .push destination false 0
    | 2 => .push destination true 0
    | _ => .halt

def pending (bit : Bool) : Fin 4 := if bit then 2 else 1

theorem pop_step [DecidableEq K] (base : Option K → List Bool) {source destination : Option K}
    (distinct : source ≠ destination) (bit : Bool) (input output : List Bool) :
    step (transfer source destination) (state (some 0) base source destination (bit :: input) output) =
      some (state (some (pending bit)) base source destination input output) := by
  cases bit <;>
    simp [step, transfer, state, instructionStep, storage_source base distinct, update_source base distinct, pending]

theorem push_step [DecidableEq K] (base : Option K → List Bool) (source destination : Option K)
    (bit : Bool) (input output : List Bool) :
    step (transfer source destination) (state (some (pending bit)) base source destination input output) =
      some (state (some 0) base source destination input (bit :: output)) := by
  cases bit <;>
    simp [step, transfer, state, instructionStep, storage_destination, update_destination, pending]

theorem empty_step [DecidableEq K] (base : Option K → List Bool) {source destination : Option K}
    (distinct : source ≠ destination) (output : List Bool) :
    step (transfer source destination) (state (some 0) base source destination [] output) =
      some (state (some 3) base source destination [] output) := by
  simp [step, transfer, state, instructionStep, storage_source base distinct, update_source base distinct]

theorem halt_step [DecidableEq K] (base : Option K → List Bool) (source destination : Option K)
    (input output : List Bool) :
    step (transfer source destination) (state (some 3) base source destination input output) =
      some (state none base source destination input output) := rfl

theorem live_storage [Fintype K] [DecidableEq K] (base : Option K → List Bool)
    {source destination : Option K} (distinct : source ≠ destination) (label) (input output : List Bool) :
    live (state label base source destination input output) + (base source).length + (base destination).length =
      live (⟨label, base⟩ : State K (Fin 4)) + input.length + output.length := by
  have first := live_update (⟨label, base⟩ : State K (Fin 4)) label source input
  change live (⟨label, Function.update base source input⟩ : State K (Fin 4)) + (base source).length =
    live (⟨label, base⟩ : State K (Fin 4)) + input.length at first
  have second := live_update (⟨label, Function.update base source input⟩ : State K (Fin 4)) label destination output
  simp only [Function.update_of_ne distinct.symm] at second
  change live (state label base source destination input output) + (base destination).length = _ at second
  omega

theorem live_move [Fintype K] [DecidableEq K] (base : Option K → List Bool)
    {source destination : Option K} (distinct : source ≠ destination) (label₁ label₂) (bit : Bool) (input output : List Bool) :
    live (state label₁ base source destination (bit :: input) output) =
      live (state label₂ base source destination input (bit :: output)) := by
  have first := live_storage base distinct label₁ (bit :: input) output
  have second := live_storage base distinct label₂ input (bit :: output)
  have same : live (⟨label₁, base⟩ : State K (Fin 4)) = live (⟨label₂, base⟩ : State K (Fin 4)) := rfl
  simp only [List.length_cons] at first second
  omega

theorem live_pop_le [Fintype K] [DecidableEq K] (base : Option K → List Bool)
    {source destination : Option K} (distinct : source ≠ destination) (label₁ label₂) (bit : Bool) (input output : List Bool) :
    live (state label₂ base source destination input output) ≤
      live (state label₁ base source destination (bit :: input) output) := by
  have first := live_storage base distinct label₁ (bit :: input) output
  have second := live_storage base distinct label₂ input output
  have same : live (⟨label₁, base⟩ : State K (Fin 4)) = live (⟨label₂, base⟩ : State K (Fin 4)) := rfl
  simp only [List.length_cons] at first second
  omega

theorem transfer_execution [Fintype K] [DecidableEq K] (base : Option K → List Bool)
    {source destination : Option K} (distinct : source ≠ destination) (input output : List Bool) :
    Execution (transfer source destination) (state (some 0) base source destination input output)
      (state none base source destination [] (input.reverse ++ output))
      (2*input.length+2) (live (state (some 0) base source destination input output)) := by
  induction input generalizing output with
  | nil =>
    have done := Execution.refl (program := transfer source destination) (state none base source destination [] output)
    have trace := Execution.cons (empty_step base distinct output) (Execution.cons (halt_step base source destination [] output) done)
    simpa [live, state] using trace
  | cons bit input ih =>
    have tail := ih (bit :: output)
    have one := Execution.cons (push_step base source destination bit input output) tail
    have two := Execution.cons (pop_step base distinct bit input output) one
    have count : (2*input.length+2)+1+1 = 2*(bit :: input).length+2 := by
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [count] at two
    have sameLive := live_move base distinct (some 0) (some 0) bit input output
    have smaller := live_pop_le base distinct (some 0) (some (pending bit)) bit input output
    simpa only [List.reverse_cons, List.singleton_append, List.append_assoc,
      ← sameLive, Nat.max_eq_right smaller, Nat.max_self] using two

def layout (shared first second : List Bool) : Option Bool → List Bool
  | none => shared
  | some false => first
  | some true => second

theorem initial_layout (program : Program Bool Q) (input : List Bool) :
    initial program input = (⟨some program.main,layout input [] []⟩ : State Bool Q) := by
  unfold initial
  congr 1
  funext port
  cases port with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem terminal_layout (output : List Bool) :
    terminal output = (⟨none,layout output [] []⟩ : State Bool Q) := by
  unfold terminal
  congr 1
  funext port
  cases port with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem live_layout (label : Option Q) (shared first second : List Bool) :
    live (⟨label, layout shared first second⟩ : State Bool Q) = shared.length + first.length + second.length := by
  simp [live, layout, Fintype.sum_option, Nat.add_assoc, Nat.add_comm]

theorem shared_to_first_start (input : List Bool) :
    storage (fun _ : Option Bool => []) none (some false) input [] = layout input [] [] := by
  funext stack
  cases stack with
  | none => simp [storage, layout]
  | some bit => cases bit <;> simp [storage, layout]

theorem shared_to_first_finish (input : List Bool) :
    storage (fun _ : Option Bool => []) none (some false) [] input = layout [] input [] := by
  funext stack
  cases stack with
  | none => simp [storage, layout]
  | some bit => cases bit <;> simp [storage, layout]

theorem first_to_second_start (input : List Bool) :
    storage (fun _ : Option Bool => []) (some false) (some true) input [] = layout [] input [] := by
  funext stack
  cases stack with
  | none => simp [storage, layout]
  | some bit => cases bit <;> simp [storage, layout]

theorem first_to_second_finish (input : List Bool) :
    storage (fun _ : Option Bool => []) (some false) (some true) [] input = layout [] [] input := by
  funext stack
  cases stack with
  | none => simp [storage, layout]
  | some bit => cases bit <;> simp [storage, layout]

theorem second_to_shared_start (input : List Bool) :
    storage (fun _ : Option Bool => []) (some true) none input [] = layout [] [] input := by
  funext stack
  cases stack with
  | none => simp [storage, layout]
  | some bit => cases bit <;> simp [storage, layout]

theorem second_to_shared_finish (input : List Bool) :
    storage (fun _ : Option Bool => []) (some true) none [] input = layout input [] [] := by
  funext stack
  cases stack with
  | none => simp [storage, layout]
  | some bit => cases bit <;> simp [storage, layout]

/-- Three linear transfers reverse a bit string and leave both private stacks empty. -/
def reverseProgram :=
  link (link (transfer (K := Bool) none (some false)) (transfer (some false) (some true)))
    (transfer (some true) none)

theorem reverse_execution (input : List Bool) :
    Execution reverseProgram (initial reverseProgram input) (terminal input.reverse)
      (6*input.length+6) input.length := by
  have first := transfer_execution (fun _ : Option Bool => [])
    (source := none) (destination := some false) (by decide) input []
  have second := transfer_execution (fun _ : Option Bool => [])
    (source := some false) (destination := some true) (by decide) input.reverse []
  have third := transfer_execution (fun _ : Option Bool => [])
    (source := some true) (destination := none) (by decide) input []
  simp only [state, List.append_nil, shared_to_first_start, shared_to_first_finish, live_layout,
    List.length_nil, Nat.add_zero] at first
  simp only [state, List.append_nil, first_to_second_start, first_to_second_finish, live_layout,
    List.length_nil, List.length_reverse, List.reverse_reverse, Nat.zero_add, Nat.add_zero] at second
  simp only [state, List.append_nil, second_to_shared_start, second_to_shared_finish, live_layout,
    List.length_nil, Nat.zero_add] at third
  have trace := (first.link second).link third
  have start : (⟨some reverseProgram.main, layout input [] []⟩ : State Bool _) = initial reverseProgram input := by
    congr 1
    funext stack
    cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl
  have finish : (⟨none, layout input.reverse [] []⟩ : State Bool _) = terminal (Q := ((Fin 4 ⊕ Fin 4) ⊕ Fin 4)) input.reverse := by
    congr 1
    funext stack
    cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl
  have ticks : (2*input.length+2+(2*input.length+2))+(2*input.length+2) = 6*input.length+6 := by omega
  rw [ticks] at trace
  change Execution reverseProgram ⟨some reverseProgram.main, layout input [] []⟩
    ⟨none, layout input.reverse [] []⟩ (6*input.length+6) _ at trace
  rw [start, finish] at trace
  simpa only [Nat.max_self] using trace

theorem reverse_computes : Computes reverseProgram List.reverse
    (Polynomial.C 6 * Polynomial.X + Polynomial.C 6) := by
  intro input
  exact ⟨6*input.length+6, input.length, reverse_execution input, by simp⟩

theorem reverse_tm_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime id id (List.reverse : List Bool → List Bool)) :=
  reverse_computes.tm_polytime

theorem transfer_resident (source destination : Option K) :
    (∑ label, statementSize (tmStatement ((transfer source destination).code label))) ≤ 36 := by
  simpa using finiteTM_resident (transfer source destination)

theorem reverse_resident :
    (∑ label, statementSize (tmStatement (reverseProgram.code label))) ≤ 108 := by
  simpa [reverseProgram] using finiteTM_resident reverseProgram

end Controller.Complexity.StackBlocks
