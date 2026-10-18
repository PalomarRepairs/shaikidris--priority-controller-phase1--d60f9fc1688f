module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordReader

@[expose] public section

/-! Finite state-shape checks validate a singleton PC field and exactly one
final halt bit. Both checks publish their result in the actual status bank;
the halt bit is moved to a persistent bank by a charged instruction. -/
namespace Controller.Complexity.StateShape
open StackMachine WordReader
open scoped BigOperators

def field (frame : Port → List Bool) (status : List Bool) (count : Nat) : Port → List Bool :=
  Function.update (Function.update frame none status) (some 12) (List.replicate count true)

theorem field_at (frame : Port → List Bool) (status : List Bool) (count : Nat) (address : Port) :
    field frame status count address=if address=some 12 then List.replicate count true else if address=none then status else frame address := by
  simp only [field,Function.update_apply]

theorem field_count_update (frame : Port → List Bool) (status : List Bool) (count replacement : Nat) :
    Function.update (field frame status count) (some 12) (List.replicate replacement true)=field frame status replacement := by
  funext address
  by_cases same : address=some 12 <;> simp_all [field_at]

theorem field_nil_update (frame : Port → List Bool) (status : List Bool) (count : Nat) :
    Function.update (field frame status count) (some 12) []=field frame status 0 := field_count_update frame status count 0

theorem field_one_update (frame : Port → List Bool) (status : List Bool) (count : Nat) :
    Function.update (field frame status count) (some 12) [true]=field frame status 1 := field_count_update frame status count 1

theorem field_cons_update (frame : Port → List Bool) (status : List Bool) (count replacement : Nat) :
    Function.update (field frame status count) (some 12) (true :: List.replicate replacement true)=field frame status (replacement+1) :=
  field_count_update frame status count (replacement+1)

theorem field_status_update (frame : Port → List Bool) (status replacement : List Bool) (count : Nat) :
    Function.update (field frame status count) none replacement=field frame replacement count := by
  funext address
  by_cases same : address=none <;> simp_all [field_at]

def singletonProgram : Program (Fin 31) (Fin 5) where
  main := 0
  code label := match label.val with
    | 0 => .pop (some 12) 3 3 1
    | 1 => .peek (some 12) 2 3 3
    | 2 => .push (some 12) true 4
    | 3 => .push none false 4
    | _ => .halt

def retainedCount (count : Nat) := if count=1 then 1 else count-1

theorem singleton_execution (frame : Port → List Bool) (count : Nat) :
    ∃ ticks peak, Execution singletonProgram ⟨some singletonProgram.main,field frame [] count⟩
      ⟨none,field frame (if count=1 then [] else [false]) (retainedCount count)⟩ ticks peak ∧ ticks ≤ 4 := by
  have last (status : List Bool) (n : Nat) : step singletonProgram ⟨some 4,field frame status n⟩=
      some ⟨none,field frame status n⟩ := rfl
  have fail (n : Nat) : step singletonProgram ⟨some 3,field frame [] n⟩=some ⟨some 4,field frame [false] n⟩ := by
    simp [step,singletonProgram,instructionStep,field_at,field_status_update]
  cases count with
  | zero =>
    have first : step singletonProgram ⟨some 0,field frame [] 0⟩=some ⟨some 3,field frame [] 0⟩ := by
      simp [step,singletonProgram,instructionStep,field_at,field_nil_update]
    have trace := Execution.cons first (Execution.cons (fail 0) (Execution.cons (last [false] 0) (Execution.refl _)))
    exact ⟨3,_,by simpa only [singletonProgram,retainedCount,Nat.zero_ne_one,ite_false,Nat.zero_sub] using trace,by decide⟩
  | succ count =>
    cases count with
    | zero =>
      have first : step singletonProgram ⟨some 0,field frame [] 1⟩=some ⟨some 1,field frame [] 0⟩ := by
        simp [step,singletonProgram,instructionStep,field_at,field_nil_update]
      have second : step singletonProgram ⟨some 1,field frame [] 0⟩=some ⟨some 2,field frame [] 0⟩ := rfl
      have restore : step singletonProgram ⟨some 2,field frame [] 0⟩=some ⟨some 4,field frame [] 1⟩ := by
        simp [step,singletonProgram,instructionStep,field_at,field_one_update]
      have trace := Execution.cons first (Execution.cons second (Execution.cons restore (Execution.cons (last [] 1) (Execution.refl _))))
      exact ⟨4,_,by simpa only [singletonProgram,retainedCount,ite_true] using trace,le_rfl⟩
    | succ count =>
      have first : step singletonProgram ⟨some 0,field frame [] (count+2)⟩=some ⟨some 1,field frame [] (count+1)⟩ := by
        simp [step,singletonProgram,instructionStep,field_at,List.replicate_succ,field_cons_update]
      have second : step singletonProgram ⟨some 1,field frame [] (count+1)⟩=some ⟨some 3,field frame [] (count+1)⟩ := rfl
      have trace := Execution.cons first (Execution.cons second (Execution.cons (fail (count+1)) (Execution.cons (last [false] (count+1)) (Execution.refl _))))
      have notOne : ¬count+2=1 := by omega
      have predecessor : count+2-1=count+1 := by omega
      exact ⟨4,_,by simpa only [singletonProgram,retainedCount,notOne,ite_false,predecessor] using trace,le_rfl⟩

theorem singleton_ready (input : Port → List Bool) (count : Nat) (status : input none=[])
    (saved : input (some 12)=List.replicate count true) :
    ∃ ticks peak, Execution singletonProgram ⟨some singletonProgram.main,input⟩
      ⟨none,field input (if count=1 then [] else [false]) (retainedCount count)⟩ ticks peak ∧ ticks ≤ 4 := by
  have entry : field input [] count=input := by simp only [field,← status,← saved,Function.update_eq_self]
  simpa only [entry] using singleton_execution input count

def tail (frame : Port → List Bool) (status source halt : List Bool) : Port → List Bool :=
  Function.update (Function.update (Function.update frame none status) (some 0) source) (some 26) halt

theorem tail_at (frame : Port → List Bool) (status source halt : List Bool) (address : Port) :
    tail frame status source halt address=
      if address=some 26 then halt else if address=some 0 then source else if address=none then status else frame address := by
  simp only [tail,Function.update_apply]

theorem tail_source_update (frame : Port → List Bool) (status source halt replacement : List Bool) :
    Function.update (tail frame status source halt) (some 0) replacement=tail frame status replacement halt := by
  funext address
  by_cases same : address=some 0 <;> simp_all [tail_at]

theorem tail_halt_update (frame : Port → List Bool) (status source halt replacement : List Bool) :
    Function.update (tail frame status source halt) (some 26) replacement=tail frame status source replacement := by
  funext address
  by_cases same : address=some 26 <;> simp_all [tail_at]

theorem tail_status_update (frame : Port → List Bool) (status source halt replacement : List Bool) :
    Function.update (tail frame status source halt) none replacement=tail frame replacement source halt := by
  funext address
  by_cases same : address=none <;> simp_all [tail_at]

def tailProgram : Program (Fin 31) (Fin 7) where
  main := 0
  code label := match label.val with
    | 0 => .pop (some 0) 5 1 2
    | 1 => .push (some 26) false 3
    | 2 => .push (some 26) true 3
    | 3 => .peek (some 0) 6 5 5
    | 5 => .push none false 6
    | _ => .halt

def tailResult (frame : Port → List Bool) (input : List Bool) : Port → List Bool :=
  match input with
  | [] => tail frame [false] [] []
  | bit :: rest => tail frame (if rest=[] then [] else [false]) rest [bit]

def decodeTail : List Bool → Option Bool
  | [bit] => some bit
  | _ => none

theorem tail_execution (frame : Port → List Bool) (input : List Bool) :
    ∃ ticks peak, Execution tailProgram ⟨some tailProgram.main,tail frame [] input []⟩
      ⟨none,tailResult frame input⟩ ticks peak ∧ ticks ≤ 5 ∧
      Option.isNone ((tailResult frame input none).head?)=(decodeTail input).isSome := by
  have last (status source halt : List Bool) : step tailProgram ⟨some 6,tail frame status source halt⟩=
      some ⟨none,tail frame status source halt⟩ := rfl
  have fail (source halt : List Bool) : step tailProgram ⟨some 5,tail frame [] source halt⟩=
      some ⟨some 6,tail frame [false] source halt⟩ := by
    simp [step,tailProgram,instructionStep,tail_at,tail_status_update]
  cases input with
  | nil =>
    have first : step tailProgram ⟨some 0,tail frame [] [] []⟩=some ⟨some 5,tail frame [] [] []⟩ := by
      simp [step,tailProgram,instructionStep,tail_at,tail_source_update]
    have trace := Execution.cons first (Execution.cons (fail [] []) (Execution.cons (last [false] [] []) (Execution.refl _)))
    exact ⟨3,_,by simpa only [tailProgram,tailResult] using trace,by decide,by simp [tailResult,tail_at,decodeTail]⟩
  | cons bit rest =>
    have first : step tailProgram ⟨some 0,tail frame [] (bit :: rest) []⟩=
        some ⟨some (if bit then 2 else 1),tail frame [] rest []⟩ := by
      cases bit <;> simp [step,tailProgram,instructionStep,tail_at,tail_source_update]
    have save : step tailProgram ⟨some (if bit then 2 else 1),tail frame [] rest []⟩=
        some ⟨some 3,tail frame [] rest [bit]⟩ := by
      cases bit <;> simp [step,tailProgram,instructionStep,tail_at,tail_halt_update]
    cases rest with
    | nil =>
      have check : step tailProgram ⟨some 3,tail frame [] [] [bit]⟩=some ⟨some 6,tail frame [] [] [bit]⟩ := rfl
      have trace := Execution.cons first (Execution.cons save (Execution.cons check (Execution.cons (last [] [] [bit]) (Execution.refl _))))
      exact ⟨4,_,by simpa only [tailProgram,tailResult,ite_true] using trace,by decide,by simp [tailResult,tail_at,decodeTail]⟩
    | cons extra rest =>
      have check : step tailProgram ⟨some 3,tail frame [] (extra :: rest) [bit]⟩=
          some ⟨some 5,tail frame [] (extra :: rest) [bit]⟩ := by cases extra <;> rfl
      have trace := Execution.cons first (Execution.cons save (Execution.cons check
        (Execution.cons (fail (extra :: rest) [bit]) (Execution.cons (last [false] (extra :: rest) [bit]) (Execution.refl _)))))
      exact ⟨5,_,by simpa only [tailProgram,tailResult,List.cons_ne_nil,ite_false] using trace,le_rfl,
        by simp [tailResult,tail_at,decodeTail]⟩

theorem tail_ready (input : Port → List Bool) (status : input none=[]) (empty : input (some 26)=[]) :
    ∃ ticks peak, Execution tailProgram ⟨some tailProgram.main,input⟩
      ⟨none,tailResult input (input (some 0))⟩ ticks peak ∧ ticks ≤ 5 ∧
      Option.isNone ((tailResult input (input (some 0)) none).head?)=(decodeTail (input (some 0))).isSome := by
  have entry : tail input [] (input (some 0)) []=input := by
    funext address
    by_cases hs : address=none <;> by_cases hi : address=some 0 <;> by_cases hh : address=some 26 <;> simp_all [tail_at]
  simpa only [entry] using tail_execution input (input (some 0))

theorem singleton_resident : (∑ label, statementSize (tmStatement (singletonProgram.code label))) ≤ 45 := by
  simpa only [Fintype.card_fin,Nat.reduceMul] using finiteTM_resident singletonProgram

theorem tail_resident : (∑ label, statementSize (tmStatement (tailProgram.code label))) ≤ 63 := by
  simpa only [Fintype.card_fin,Nat.reduceMul] using finiteTM_resident tailProgram

end Controller.Complexity.StateShape
