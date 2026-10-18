module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.RegisterRange

public import Mathlib.Tactic.Ring

@[expose] public section

/-! The saved unary register count is checked against binary word capacity.
The routine compares an all-ones word with one less than the count, then
inverts that result. No stack of length `2^width` is constructed. -/
namespace Controller.Complexity.RegisterCapacity
open StackMachine WordReader
open scoped BigOperators
abbrev bank := RegisterRange.bank

theorem ones_value (width : Nat) : Encoding.value (List.replicate width true)+1=2^width := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [List.replicate_succ, Encoding.value, ite_true, Nat.pow_succ]; omega

theorem capacity_test (width registers : Nat) :
    Encoding.value (List.replicate width true) < registers-1 ↔ 2^width < registers := by
  have value := ones_value width
  omega

def widthPorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 8) (some 1) (some 17) (by decide) (by decide) (by decide)

theorem widthPorts_apply (port : Option Bool) : widthPorts port=
    (match port with | none => some 8 | some false => some 1 | some true => some 17) := rfl

def widthMachine := StackFrames.relocate widthPorts StackCopy.program

theorem width_execution (frame : Port → List Bool) (width registers : Nat)
    (stored : frame (some 8)=List.replicate width true) :
    ∃ peak, Execution widthMachine
      ⟨some widthMachine.main,bank frame [] [] (List.replicate registers true) []⟩
      ⟨none,bank frame [] (List.replicate width true) (List.replicate registers true) []⟩ (5*width+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution widthPorts (bank frame [] [] (List.replicate registers true) [])
    (by simp [widthPorts_apply, RegisterRange.bank_at])
  have output : Function.update (bank frame [] [] (List.replicate registers true) []) (widthPorts (some false))
      (bank frame [] [] (List.replicate registers true) [] (widthPorts none)++
        bank frame [] [] (List.replicate registers true) [] (widthPorts (some false)))=
      bank frame [] (List.replicate width true) (List.replicate registers true) [] := by
    funext target
    by_cases hw : target=some 1 <;> simp_all [widthPorts_apply, RegisterRange.bank_at]
  rw [output] at trace
  exact ⟨peak,by simpa [widthMachine, StackFrames.relocate, widthPorts_apply, RegisterRange.bank_at, stored] using trace⟩

theorem bound_update (frame : Port → List Bool) (status word bound scratch replacement : List Bool) :
    Function.update (bank frame status word bound scratch) (some 16) replacement=bank frame status word replacement scratch := by
  funext target
  by_cases hb : target=some 16 <;> simp_all [RegisterRange.bank_at]

theorem word_update (frame : Port → List Bool) (status word bound scratch replacement : List Bool) :
    Function.update (bank frame status word bound scratch) (some 1) replacement=bank frame status replacement bound scratch := by
  funext target
  by_cases hw : target=some 1 <;> simp_all [RegisterRange.bank_at]

theorem status_update (frame : Port → List Bool) (status word bound scratch replacement : List Bool) :
    Function.update (bank frame status word bound scratch) none replacement=bank frame replacement word bound scratch := by
  funext target
  by_cases hs : target=none <;> simp_all [RegisterRange.bank_at]

def dropProgram : Program (Fin 31) (Fin 2) where
  main := 0
  code label := if label=0 then .pop (some 16) 1 1 1 else .halt

theorem drop_execution (frame : Port → List Bool) (word : List Bool) (registers : Nat) :
    ∃ peak, Execution dropProgram ⟨some dropProgram.main,bank frame [] word (List.replicate registers true) []⟩
      ⟨none,bank frame [] word (List.replicate (registers-1) true) []⟩ 2 peak := by
  have first : step dropProgram ⟨some dropProgram.main,bank frame [] word (List.replicate registers true) []⟩=
      some ⟨some 1,bank frame [] word (List.replicate (registers-1) true) []⟩ := by
    cases registers <;> simp [step, dropProgram, instructionStep, RegisterRange.bank_at, bound_update, List.replicate_succ]
  have last : step dropProgram ⟨some 1,bank frame [] word (List.replicate (registers-1) true) []⟩=
      some ⟨none,bank frame [] word (List.replicate (registers-1) true) []⟩ := by simp [step, dropProgram, instructionStep]
  exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩

def invertProgram : Program (Fin 31) (Fin 3) where
  main := 0
  code label := match label.val with
    | 0 => .pop (some 1) 1 2 1
    | 1 => .push none false 2
    | _ => .halt

theorem invert_execution (frame : Port → List Bool) (accepted : Prop) [Decidable accepted] :
    ∃ ticks peak, Execution invertProgram
      ⟨some invertProgram.main,bank frame [] (if accepted then [false] else []) [] []⟩
      ⟨none,bank frame (if accepted then [] else [false]) [] [] []⟩ ticks peak ∧ ticks ≤ 3 := by
  have last (status : List Bool) : step invertProgram ⟨some 2,bank frame status [] [] []⟩=
      some ⟨none,bank frame status [] [] []⟩ := rfl
  by_cases valid : accepted
  · have first : step invertProgram ⟨some invertProgram.main,bank frame [] [false] [] []⟩=
        some ⟨some 2,bank frame [] [] [] []⟩ := by simp [step, invertProgram, instructionStep, RegisterRange.bank_at, word_update]
    have trace := Execution.cons first (Execution.cons (last []) (Execution.refl _))
    exact ⟨2,_,by simpa only [ite_eq_left valid] using trace,by decide⟩
  · have first : step invertProgram ⟨some invertProgram.main,bank frame [] [] [] []⟩=
        some ⟨some 1,bank frame [] [] [] []⟩ := by simp [step, invertProgram, instructionStep, RegisterRange.bank_at, word_update]
    have flag : step invertProgram ⟨some 1,bank frame [] [] [] []⟩=
        some ⟨some 2,bank frame [false] [] [] []⟩ := by simp [step, invertProgram, instructionStep, RegisterRange.bank_at, status_update]
    have trace := Execution.cons first (Execution.cons flag (Execution.cons (last [false]) (Execution.refl _)))
    exact ⟨3,_,by simpa only [ite_eq_right valid] using trace,le_rfl⟩

def setup := link (link RegisterRange.copyMachine widthMachine) dropProgram
def program := link (link setup RegisterRange.coreMachine) invertProgram

theorem execution (frame : Port → List Bool) (width registers : Nat)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] [] [] []⟩
      ⟨none,bank frame (if registers ≤ 2^width then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ width*(4*registers+10)+6*registers+18 := by
  obtain ⟨copyPeak,copying⟩ := RegisterRange.copy_execution frame [] registers saved
  obtain ⟨widthPeak,widthRun⟩ := width_execution frame width registers stored
  obtain ⟨dropPeak,dropping⟩ := drop_execution frame (List.replicate width true) registers
  obtain ⟨coreTicks,corePeak,checking,coreBound⟩ := RegisterRange.core_execution frame (List.replicate width true) (registers-1)
  have flag : (if Encoding.value (List.replicate width true) < registers-1 then [] else [false])=
      (if registers ≤ 2^width then [false] else []) := by
    have equivalence := capacity_test width registers
    by_cases valid : registers ≤ 2^width <;> simp_all
  rw [flag] at checking
  obtain ⟨invertTicks,invertPeak,inverting,invertBound⟩ := invert_execution frame (registers ≤ 2^width)
  have trace := (((copying.link widthRun).link dropping).link checking).link inverting
  simp only [List.length_replicate] at coreBound
  have shrink : registers-1 ≤ registers := Nat.sub_le _ _
  have product := Nat.mul_le_mul_left width (show 4*(registers-1)+5 ≤ 4*registers+5 by omega)
  have identity : (5*registers+4)+(5*width+4)+2+(width*(4*registers+5)+registers+5)+3=
      width*(4*registers+10)+6*registers+18 := by ring
  exact ⟨_,_,trace,by omega⟩

theorem ready_execution (input : Port → List Bool) (width registers : Nat)
    (stored : input (some 8)=List.replicate width true) (saved : input (some 9)=List.replicate registers true)
    (clean : input none=[]) (word : input (some 1)=[]) (bound : input (some 16)=[]) (scratch : input (some 17)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩
      ⟨none,bank input (if registers ≤ 2^width then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ width*(4*registers+10)+6*registers+18 := by
  have entry : bank input [] [] [] []=input := by
    funext target
    by_cases hs : target=none <;> by_cases hw : target=some 1 <;> by_cases hb : target=some 16 <;>
      by_cases ht : target=some 17 <;> simp_all [RegisterRange.bank_at]
  simpa only [entry] using execution input width registers stored saved

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 369 := by
  simpa only [Fintype.card_sum, Fintype.card_fin, WordBound.Label, WordBound.BodyLabel, Fintype.card_option,
    Nat.reduceAdd, Nat.reduceMul] using finiteTM_resident program

def size (frame : Port → List Bool) : Nat := ∑ port : Port, (bank frame [] [] [] [] port).length

theorem cell_bound (frame : Port → List Bool) (port : Port) : (bank frame [] [] [] [] port).length ≤ size frame :=
  Finset.single_le_sum (f := fun target : Port => (bank frame [] [] [] [] target).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)

theorem total_polynomial (frame : Port → List Bool) (width registers : Nat)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] [] [] []⟩
      ⟨none,bank frame (if registers ≤ 2^width then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ 4*(size frame)^2+16*size frame+18 ∧ peak ≤ 4*(size frame)^2+17*size frame+18 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution frame width registers stored saved
  have widthBound : width ≤ size frame := by simpa [RegisterRange.bank_at, stored] using cell_bound frame (some 8)
  have registerBound : registers ≤ size frame := by simpa [RegisterRange.bank_at, saved] using cell_bound frame (some 9)
  have product := Nat.mul_le_mul widthBound (Nat.add_le_add_right (Nat.mul_le_mul_left 4 registerBound) 10)
  have identity : size frame*(4*size frame+10)+6*size frame+18=4*(size frame)^2+16*size frame+18 := by ring
  have finalTime : ticks ≤ 4*(size frame)^2+16*size frame+18 := by rw [← identity]; omega
  have space := trace.peak_le
  change peak ≤ size frame+ticks at space
  have peakIdentity : size frame+(4*(size frame)^2+16*size frame+18)=4*(size frame)^2+17*size frame+18 := by ring
  exact ⟨ticks,peak,trace,finalTime,space.trans ((Nat.add_le_add_left finalTime _).trans_eq peakIdentity)⟩

end Controller.Complexity.RegisterCapacity
