module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.StackFrames

@[expose] public section

/-! Finite binary-stack programs halve a unary bound. A true index bit uses
floor division; a false bit uses ceiling division. The destination can retain
an existing suffix, and the third stack is unchanged. -/
namespace Controller.Complexity.UnaryHalf
open StackMachine StackBlocks
open scoped BigOperators

def shrink (bit : Bool) (bound : Nat) : Nat := if bit then bound/2 else (bound+1)/2

theorem shrink_le (bit : Bool) (bound : Nat) : shrink bit bound ≤ bound := by
  cases bit <;> simp only [shrink, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem comparison (bit : Bool) (tail bound : Nat) :
    2*tail+(if bit then 1 else 0) < bound ↔ tail < shrink bit bound := by
  cases bit <;> simp only [shrink, Bool.false_eq_true, ite_false, ite_true] <;> omega

def program (bit : Bool) : Program Bool (Fin 7) where
  main := if bit then 0 else 3
  code label := match label.val with
    | 0 => .pop none 6 1 1
    | 1 => .pop none 6 2 2
    | 2 => .push (some false) true 0
    | 3 => .pop none 6 4 4
    | 4 => .push (some false) true 5
    | 5 => .pop none 6 3 3
    | _ => .halt

def state (label : Option (Fin 7)) (source destination spare : List Bool) : State Bool (Fin 7) :=
  ⟨label,layout source destination spare⟩

theorem pop_step (bit : Bool) (label next : Fin 7) (destination spare : List Bool) (source : List Bool)
    (code : (program bit).code label = .pop none 6 next next) :
    step (program bit) (state (some label) (true :: source) destination spare) =
      some (state (some next) source destination spare) := by
  simp [step, state, code, instructionStep, layout]
  funext port
  cases port with
  | none => rfl
  | some value => cases value <;> rfl

theorem empty_step (bit : Bool) (label next : Fin 7) (destination spare : List Bool)
    (code : (program bit).code label = .pop none 6 next next) :
    step (program bit) (state (some label) [] destination spare) =
      some (state (some 6) [] destination spare) := by
  simp [step, state, code, instructionStep, layout]

theorem push_step (bit : Bool) (label next : Fin 7) (source destination spare : List Bool)
    (code : (program bit).code label = .push (some false) true next) :
    step (program bit) (state (some label) source destination spare) =
      some (state (some next) source (true :: destination) spare) := by
  simp [step, state, code, instructionStep, layout]
  funext port
  cases port with
  | none => rfl
  | some value => cases value <;> rfl

theorem halt_step (bit : Bool) (destination spare : List Bool) :
    step (program bit) (state (some 6) [] destination spare)=some (state none [] destination spare) := rfl

theorem floor_execution (count : Nat) (destination spare : List Bool) :
    ∃ peak, Execution (program true) (state (some 0) (List.replicate count true) destination spare)
      (state none [] (List.replicate (count/2) true++destination) spare) (count+count/2+2) peak := by
  induction count using Nat.twoStepInduction generalizing destination with
  | zero =>
    have trace := Execution.cons (empty_step true 0 1 destination spare rfl)
      (Execution.cons (halt_step true destination spare) (Execution.refl _))
    exact ⟨_,by simpa using trace⟩
  | one =>
    have trace := Execution.cons (pop_step true 0 1 destination spare [] rfl)
      (Execution.cons (empty_step true 1 2 destination spare rfl)
        (Execution.cons (halt_step true destination spare) (Execution.refl _)))
    exact ⟨_,by simpa using trace⟩
  | more count ih _ =>
    obtain ⟨peak,tail⟩ := ih (true :: destination)
    have trace := Execution.cons (pop_step true 0 1 destination spare (true :: List.replicate count true) rfl)
      (Execution.cons (pop_step true 1 2 destination spare (List.replicate count true) rfl)
        (Execution.cons (push_step true 2 0 (List.replicate count true) destination spare rfl) tail))
    have half : (count+2)/2=count/2+1 := by omega
    have result : List.replicate (count/2) true++(true :: destination)=List.replicate ((count+2)/2) true++destination := by
      rw [half, List.replicate_succ', List.append_assoc]
      rfl
    have ticks : ((count+count/2+2)+1)+1+1=(count+2)+(count+2)/2+2 := by omega
    exact ⟨_,by simpa only [List.replicate_succ, result, ticks] using trace⟩

theorem ceil_execution (count : Nat) (destination spare : List Bool) :
    ∃ peak, Execution (program false) (state (some 3) (List.replicate count true) destination spare)
      (state none [] (List.replicate ((count+1)/2) true++destination) spare) (count+(count+1)/2+2) peak := by
  induction count using Nat.twoStepInduction generalizing destination with
  | zero =>
    have trace := Execution.cons (empty_step false 3 4 destination spare rfl)
      (Execution.cons (halt_step false destination spare) (Execution.refl _))
    exact ⟨_,by simpa using trace⟩
  | one =>
    have trace := Execution.cons (pop_step false 3 4 destination spare [] rfl)
      (Execution.cons (push_step false 4 5 [] destination spare rfl)
        (Execution.cons (empty_step false 5 3 (true :: destination) spare rfl)
          (Execution.cons (halt_step false (true :: destination) spare) (Execution.refl _))))
    exact ⟨_,by simpa using trace⟩
  | more count ih _ =>
    obtain ⟨peak,tail⟩ := ih (true :: destination)
    have trace := Execution.cons (pop_step false 3 4 destination spare (true :: List.replicate count true) rfl)
      (Execution.cons (push_step false 4 5 (true :: List.replicate count true) destination spare rfl)
        (Execution.cons (pop_step false 5 3 (true :: destination) spare (List.replicate count true) rfl) tail))
    have half : (count+2+1)/2=(count+1)/2+1 := by omega
    have result : List.replicate ((count+1)/2) true++(true :: destination)=List.replicate ((count+2+1)/2) true++destination := by
      rw [half, List.replicate_succ', List.append_assoc]
      rfl
    have ticks : ((count+(count+1)/2+2)+1)+1+1=(count+2)+(count+2+1)/2+2 := by omega
    exact ⟨_,by simpa only [List.replicate_succ, result, ticks] using trace⟩

theorem execution (bit : Bool) (count : Nat) (destination spare : List Bool) :
    ∃ peak, Execution (program bit) (state (some (program bit).main) (List.replicate count true) destination spare)
      (state none [] (List.replicate (shrink bit count) true++destination) spare) (count+shrink bit count+2) peak := by
  cases bit
  · exact ceil_execution count destination spare
  · exact floor_execution count destination spare

theorem resident (bit : Bool) : (∑ label, statementSize (tmStatement ((program bit).code label))) ≤ 63 :=
  finiteTM_resident (program bit)

end Controller.Complexity.UnaryHalf
