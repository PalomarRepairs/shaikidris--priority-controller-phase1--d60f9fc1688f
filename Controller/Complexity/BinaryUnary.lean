module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.UnaryDouble
public import Controller.Complexity.WordReader
public import Mathlib.Tactic.Ring

@[expose] public section

/-! A finite Horner scan converts most-significant-first binary digits to a
unary counter. Its cost is bounded in the resulting counter length. A caller
must check the index against stored data length before using this conversion. -/
namespace Controller.Complexity.BinaryUnary
open StackMachine StackBlocks WordReader
open scoped BigOperators

def digit (bit : Bool) : Nat := if bit then 1 else 0

def fold (initial : Nat) : List Bool → Nat
  | [] => initial
  | bit :: rest => fold (2*initial+digit bit) rest

theorem fold_ge (initial : Nat) (word : List Bool) : initial ≤ fold initial word := by
  induction word generalizing initial with
  | nil => rfl
  | cons bit word ih => have bound := ih (2*initial+digit bit); simp only [fold]; omega

theorem value_append (left right : List Bool) : Encoding.value (left++right)=Encoding.value left+2^left.length*Encoding.value right := by
  induction left with
  | nil => simp [Encoding.value]
  | cons bit left ih => simp only [List.cons_append,Encoding.value,ih,List.length_cons,Nat.pow_succ]; ring

theorem fold_value (initial : Nat) (word : List Bool) : fold initial word=2^word.length*initial+Encoding.value word.reverse := by
  induction word generalizing initial with
  | nil => simp [fold,Encoding.value]
  | cons bit word ih =>
    simp only [fold,ih,List.reverse_cons,value_append,List.length_reverse,List.length_cons,Nat.pow_succ,
      Encoding.value,digit]
    ring

def bank (frame : Port → List Bool) (word : List Bool) (count : Nat) (temporary mode scratch : List Bool) : Port → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update frame (some 6) word)
    (some 4) (List.replicate count true)) (some 5) temporary) (some 7) mode) (some 17) scratch

theorem bank_at (frame : Port → List Bool) (word : List Bool) (count : Nat) (temporary mode scratch : List Bool) (address : Port) :
    bank frame word count temporary mode scratch address=
      if address=some 17 then scratch else if address=some 7 then mode else if address=some 5 then temporary
      else if address=some 4 then List.replicate count true else if address=some 6 then word else frame address := by
  simp only [bank,Function.update_apply]

theorem word_update (frame : Port → List Bool) (word replacement : List Bool) (count : Nat) (temporary mode scratch : List Bool) :
    Function.update (bank frame word count temporary mode scratch) (some 6) replacement=bank frame replacement count temporary mode scratch := by
  funext address
  by_cases same : address=some 6 <;> simp_all [bank_at]

theorem mode_update (frame : Port → List Bool) (word : List Bool) (count : Nat) (temporary mode scratch replacement : List Bool) :
    Function.update (bank frame word count temporary mode scratch) (some 7) replacement=bank frame word count temporary replacement scratch := by
  funext address
  by_cases same : address=some 7 <;> simp_all [bank_at]

theorem count_succ_update (frame : Port → List Bool) (word : List Bool) (count : Nat) (temporary mode scratch : List Bool) :
    Function.update (bank frame word count temporary mode scratch) (some 4) (true :: List.replicate count true)=
      bank frame word (count+1) temporary mode scratch := by
  funext address
  by_cases same : address=some 4 <;> simp_all [bank_at,List.replicate_succ]

def doublePorts : Option Bool ↪ Port := StackFrames.threePorts (some 4) (some 5) (some 17) (by decide) (by decide) (by decide)

theorem doublePorts_apply (port : Option Bool) : doublePorts port=(match port with | none => some 4 | some false => some 5 | some true => some 17) := rfl

def doubleMachine := StackFrames.relocate doublePorts UnaryDouble.program

theorem double_storage (frame : Port → List Bool) (word mode : List Bool) (count : Nat) (temporary scratch : List Bool) :
    StackFrames.embedStorage doublePorts (bank frame word 0 [] mode []) (layout (List.replicate count true) temporary scratch)=
      bank frame word count temporary mode scratch := by
  funext address
  by_cases hc : address=some 4 <;> by_cases ht : address=some 5 <;> by_cases hs : address=some 17 <;>
    simp_all [StackFrames.embedStorage,doublePorts_apply,layout,bank_at]

theorem double_execution (frame : Port → List Bool) (word mode : List Bool) (count : Nat) :
    ∃ peak, Execution doubleMachine ⟨some doubleMachine.main,bank frame word count [] mode []⟩
      ⟨none,bank frame word (2*count) [] mode []⟩ (7*count+6) peak := by
  obtain ⟨peak,trace⟩ := UnaryDouble.execution count
  have relocated := StackFrames.execution doublePorts (bank frame word 0 [] mode []) trace
  exact ⟨_,by simpa only [doubleMachine,StackFrames.relocate,StackFrames.embedState,double_storage] using relocated⟩

def seed (bit : Bool) : Program (Fin 31) (Fin 3) where
  main := if bit then 1 else 0
  code label := match label.val with
    | 0 => .push (some 7) false 2
    | 1 => .push (some 7) true 2
    | _ => .halt

def finish : Program (Fin 31) (Fin 3) where
  main := 0
  code label := match label.val with
    | 0 => .pop (some 7) 2 2 1
    | 1 => .push (some 4) true 2
    | _ => .halt

theorem seed_execution (frame : Port → List Bool) (word : List Bool) (count : Nat) (bit : Bool) :
    ∃ peak, Execution (seed bit) ⟨some (seed bit).main,bank frame word count [] [] []⟩
      ⟨none,bank frame word count [] [bit] []⟩ 2 peak := by
  have first : step (seed bit) ⟨some (seed bit).main,bank frame word count [] [] []⟩=
      some ⟨some 2,bank frame word count [] [bit] []⟩ := by cases bit <;> simp [step,seed,instructionStep,bank_at,mode_update]
  have last : step (seed bit) ⟨some 2,bank frame word count [] [bit] []⟩=some ⟨none,bank frame word count [] [bit] []⟩ := rfl
  exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩

theorem finish_execution (frame : Port → List Bool) (word : List Bool) (count : Nat) (bit : Bool) :
    ∃ peak, Execution finish ⟨some finish.main,bank frame word count [] [bit] []⟩
      ⟨none,bank frame word (count+digit bit) [] [] []⟩ (2+digit bit) peak := by
  have last (n : Nat) : step finish ⟨some 2,bank frame word n [] [] []⟩=some ⟨none,bank frame word n [] [] []⟩ := rfl
  cases bit with
  | false =>
    have first : step finish ⟨some finish.main,bank frame word count [] [false] []⟩=
        some ⟨some 2,bank frame word count [] [] []⟩ := by simp [step,finish,instructionStep,bank_at,mode_update]
    exact ⟨_,by simpa only [digit,Bool.false_eq_true,ite_false,Nat.add_zero] using Execution.cons first (Execution.cons (last count) (Execution.refl _))⟩
  | true =>
    have first : step finish ⟨some finish.main,bank frame word count [] [true] []⟩=
        some ⟨some 1,bank frame word count [] [] []⟩ := by simp [step,finish,instructionStep,bank_at,mode_update]
    have push : step finish ⟨some 1,bank frame word count [] [] []⟩=
        some ⟨some 2,bank frame word (count+1) [] [] []⟩ := by simp [step,finish,instructionStep,bank_at,count_succ_update]
    exact ⟨_,by simpa only [digit,ite_true] using Execution.cons first (Execution.cons push (Execution.cons (last (count+1)) (Execution.refl _)))⟩

def cycle (bit : Bool) := link (link (seed bit) doubleMachine) finish
abbrev CycleLabel := (Fin 3 ⊕ ((Fin 4 ⊕ Fin 6) ⊕ Fin 4)) ⊕ Fin 3
abbrev Label := CycleLabel ⊕ Option (Fin 1)

theorem cycle_code (bit : Bool) : (cycle bit).code=(cycle false).code := rfl

theorem cycle_execution (frame : Port → List Bool) (word : List Bool) (count : Nat) (bit : Bool) :
    ∃ peak, Execution (cycle bit) ⟨some (cycle bit).main,bank frame word count [] [] []⟩
      ⟨none,bank frame word (2*count+digit bit) [] [] []⟩ (7*count+10+digit bit) peak := by
  obtain ⟨seedPeak,seeding⟩ := seed_execution frame word count bit
  obtain ⟨doublePeak,doubling⟩ := double_execution frame word [bit] count
  obtain ⟨finishPeak,finishing⟩ := finish_execution frame word (2*count) bit
  have trace := (seeding.link doubling).link finishing
  have ticks : 2+(7*count+6)+(2+digit bit)=7*count+10+digit bit := by omega
  exact ⟨_,by simpa only [cycle,ticks] using trace⟩

def program : Program (Fin 31) Label where
  main := .inr (some 0)
  code label := match label with
    | .inl label => GuardedLink.leftInstruction none (0 : Fin 1) (fun _ => true) ((cycle false).code label)
    | .inr none => .halt
    | .inr (some _) => .pop (some 6) (.inr none) (.inl (cycle false).main) (.inl (cycle true).main)

theorem body_step (bit : Bool) {current next : State (Fin 31) CycleLabel} (transition : step (cycle bit) current=some next) :
    step program (GuardedLink.leftState none (0 : Fin 1) (fun _ => true) current)=
      some (GuardedLink.leftState none (0 : Fin 1) (fun _ => true) next) := by
  cases position : current.pc with
  | none => simp [step,position] at transition
  | some label =>
    have equal : instructionStep ((cycle bit).code label) current=next := by simpa [step,position] using transition
    simp only [step,GuardedLink.leftState,position,Option.elim_some,Option.map_some,program]
    rw [← congrFun (cycle_code bit) label]
    exact congrArg some ((GuardedLink.leftInstruction_step none (0 : Fin 1) (fun _ => true) ((cycle bit).code label) current).trans
      (congrArg (GuardedLink.leftState none (0 : Fin 1) (fun _ => true)) equal))

theorem body_execution (bit : Bool) {current final : State (Fin 31) CycleLabel} {ticks peak}
    (trace : Execution (cycle bit) current final ticks peak) :
    Execution program (GuardedLink.leftState none (0 : Fin 1) (fun _ => true) current)
      (GuardedLink.leftState none (0 : Fin 1) (fun _ => true) final) ticks peak := by
  induction trace with
  | refl current => exact Execution.refl _
  | cons transition tail ih => exact Execution.cons (body_step bit transition) ih

theorem read_step (frame : Port → List Bool) (word : List Bool) (count : Nat) (bit : Bool) :
    step program ⟨some program.main,bank frame (bit :: word) count [] [] []⟩=
      some (GuardedLink.leftState none (0 : Fin 1) (fun _ => true)
        (⟨some (cycle bit).main,bank frame word count [] [] []⟩ : State (Fin 31) CycleLabel)) := by
  cases bit <;> simp [step,program,instructionStep,bank_at,word_update,GuardedLink.leftState]

theorem empty_execution (frame : Port → List Bool) (count : Nat) :
    ∃ peak, Execution program ⟨some program.main,bank frame [] count [] [] []⟩
      ⟨none,bank frame [] count [] [] []⟩ 2 peak := by
  have first : step program ⟨some program.main,bank frame [] count [] [] []⟩=
      some ⟨some (.inr none),bank frame [] count [] [] []⟩ := by simp [step,program,instructionStep,bank_at,word_update]
  have last : step program ⟨some (.inr none),bank frame [] count [] [] []⟩=some ⟨none,bank frame [] count [] [] []⟩ := rfl
  exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩

theorem execution (frame : Port → List Bool) (word : List Bool) (initial : Nat) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame word initial [] [] []⟩
      ⟨none,bank frame [] (fold initial word) [] [] []⟩ ticks peak ∧
      ticks ≤ word.length*(7*fold initial word+12)+2 := by
  induction word generalizing initial with
  | nil => obtain ⟨peak,trace⟩ := empty_execution frame initial; exact ⟨2,peak,trace,by simp [fold]⟩
  | cons bit word ih =>
    obtain ⟨tailTicks,tailPeak,tail,tailBound⟩ := ih (2*initial+digit bit)
    obtain ⟨cyclePeak,cycling⟩ := cycle_execution frame word initial bit
    have lifted := body_execution bit cycling
    have boundary : GuardedLink.leftState none (0 : Fin 1) (fun _ => true)
        (⟨none,bank frame word (2*initial+digit bit) [] [] []⟩ : State (Fin 31) CycleLabel)=
        (⟨some program.main,bank frame word (2*initial+digit bit) [] [] []⟩ : State (Fin 31) Label) := by
      simp [GuardedLink.leftState,GuardedLink.exitLabel,program]
    rw [boundary] at lifted
    have trace := Execution.cons (read_step frame word initial bit) (lifted.append tail)
    have smaller := fold_ge (2*initial+digit bit) word
    have bitBound : digit bit ≤ 1 := by cases bit <;> decide
    refine ⟨(7*initial+10+digit bit)+tailTicks+1,_,trace,?_⟩
    simp only [List.length_cons,fold,Nat.add_mul,Nat.one_mul]
    omega

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 198 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.BinaryUnary
