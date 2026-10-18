module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.RegisterRange
public import Controller.Complexity.WidthReader

public import Mathlib.Tactic.Ring

@[expose] public section

/-! The next saved role bit selects an executed register-range check or
discards an immediate word. Missing role data sets the error flag. -/
namespace Controller.Complexity.OperandCheck
open StackMachine WordReader
open scoped BigOperators

abbrev Label := Fin 4 ⊕ RegisterRange.Label

def program : Program (Fin 31) Label where
  main := .inl 0
  code label := match label with
    | .inr label => linkRightInstruction (RegisterRange.program.code label)
    | .inl label => match label.val with
      | 0 => .pop (some 18) (.inl 2) (.inl 1) (.inr RegisterRange.program.main)
      | 1 => .pop (some 1) (.inl 3) (.inl 1) (.inl 1)
      | 2 => .push none false (.inl 3)
      | _ => .halt

theorem range_step {state next} (transition : step RegisterRange.program state=some next) :
    step program (linkRightState (Q₁ := Fin 4) state)=some (linkRightState next) := by
  cases position : state.pc with
  | none => simp [step, position] at transition
  | some label =>
    have next_eq : instructionStep (RegisterRange.program.code label) state=next := by
      simpa [step, position] using transition
    simp only [step, linkRightState, position, Option.map_some, program]
    exact congrArg some ((linkRightInstruction_step (Q₁ := Fin 4) (RegisterRange.program.code label) state).trans
      (congrArg linkRightState next_eq))

theorem range_execution {state final ticks peak} (trace : Execution RegisterRange.program state final ticks peak) :
    Execution program (linkRightState (Q₁ := Fin 4) state) (linkRightState final) ticks peak := by
  induction trace with
  | refl => exact Execution.refl _
  | cons transition tail ih => exact Execution.cons (range_step transition) ih

theorem select_step (input : Port → List Bool) (bit : Bool) (rest : List Bool)
    (stored : input (some 18)=bit :: rest) :
    step program ⟨some program.main,input⟩=
      some ⟨some (if bit then .inr RegisterRange.program.main else .inl 1),Function.update input (some 18) rest⟩ := by
  cases bit <;> simp [step, program, instructionStep, stored]

theorem clear_step (input : Port → List Bool) (bit : Bool) (rest : List Bool)
    (stored : input (some 1)=bit :: rest) :
    step program ⟨some (.inl 1),input⟩=some ⟨some (.inl 1),Function.update input (some 1) rest⟩ := by
  cases bit <;> simp [step, program, instructionStep, stored]

theorem clear_execution (input : Port → List Bool) (word : List Bool) :
    ∃ peak, Execution program ⟨some (.inl 1),Function.update input (some 1) word⟩
      ⟨none,Function.update input (some 1) []⟩ (word.length+2) peak := by
  induction word with
  | nil =>
    have first : step program ⟨some (.inl 1),Function.update input (some 1) []⟩=
        some ⟨some (.inl 3),Function.update input (some 1) []⟩ := by simp [step, program, instructionStep]
    have last : step program ⟨some (.inl 3),Function.update input (some 1) []⟩=
        some ⟨none,Function.update input (some 1) []⟩ := rfl
    exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩
  | cons bit word ih =>
    obtain ⟨peak,tail⟩ := ih
    have first := clear_step (Function.update input (some 1) (bit :: word)) bit word (by simp)
    simp only [Function.update_idem] at first
    exact ⟨_,by simpa only [List.length_cons, Nat.add_right_comm] using Execution.cons first tail⟩

theorem immediate_execution (input : Port → List Bool) (rest : List Bool)
    (stored : input (some 18)=false :: rest) :
    ∃ peak, Execution program ⟨some program.main,input⟩
      ⟨none,Function.update (Function.update input (some 18) rest) (some 1) []⟩
      ((input (some 1)).length+3) peak := by
  let data := Function.update input (some 18) rest
  have sameWord : data (some 1)=input (some 1) := by simp [data]
  have same : Function.update data (some 1) (input (some 1))=data := by
    rw [← sameWord]
    exact Function.update_eq_self (some 1) data
  obtain ⟨peak,tail⟩ := clear_execution data (input (some 1))
  rw [same] at tail
  have first := select_step input false rest stored
  exact ⟨_,by simpa only [Bool.false_eq_true, ite_false, Nat.add_assoc] using Execution.cons first tail⟩

theorem register_execution (input : Port → List Bool) (registers : Nat) (rest : List Bool)
    (stored : input (some 18)=true :: rest) (clean : input none=[])
    (boundClean : input (some 16)=[]) (scratchClean : input (some 17)=[])
    (saved : input (some 9)=List.replicate registers true) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩
      ⟨none,RegisterRange.bank (Function.update input (some 18) rest)
        (if Encoding.value (input (some 1)) < registers then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ (input (some 1)).length*(4*registers+5)+6*registers+14 := by
  let data := Function.update input (some 18) rest
  obtain ⟨ticks,peak,tail,bound⟩ := RegisterRange.ready_execution data registers
    (by simp [data, clean]) (by simp [data, boundClean]) (by simp [data, scratchClean]) (by simp [data, saved])
  have lifted := range_execution tail
  have first := select_step input true rest stored
  have trace := Execution.cons first lifted
  refine ⟨ticks+1,max (live (⟨some program.main,input⟩ : State (Fin 31) Label)) peak,?_,?_⟩
  · simpa only [Bool.true_eq, ite_true, linkRightState, Option.map_some, Option.map_none, data,
      Function.update_of_ne (show (some 1 : Port) ≠ some 18 by decide)] using trace
  · simp only [data, Function.update_of_ne (show (some 1 : Port) ≠ some 18 by decide)] at bound
    omega

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 306 := by
  simpa only [Fintype.card_sum, Fintype.card_fin, RegisterRange.Label, WordBound.Label, WordBound.BodyLabel,
    Fintype.card_option, Fintype.card_sum, Fintype.card_fin] using finiteTM_resident program

def reader := GuardedLink.program WidthReader.program program none Option.isNone

theorem read_register (frame : Port → List Bool) (word suffix rest : List Bool) (registers : Nat)
    (widthStored : frame (some 8)=List.replicate word.length true)
    (roleStored : frame (some 18)=true :: rest) (boundClean : frame (some 16)=[])
    (scratchClean : frame (some 17)=[]) (saved : frame (some 9)=List.replicate registers true) :
    ∃ ticks peak, Execution reader
      ⟨some reader.main,WordReader.bank frame [] (word++suffix) []⟩
      ⟨none,RegisterRange.bank (Function.update (WordReader.bank frame [] suffix word) (some 18) rest)
        (if Encoding.value word < registers then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ word.length*(4*registers+19)+6*registers+26 := by
  have reading := WidthReader.execution frame word suffix widthStored
  obtain ⟨ticks,peak,checking,bound⟩ := register_execution (WordReader.bank frame [] suffix word) registers rest
    (by simpa only [bank_other frame [] suffix word (some 18) (by decide) (by decide) (by decide) (by decide)] using roleStored)
    (bank_counter frame [] suffix word)
    (by simpa only [bank_other frame [] suffix word (some 16) (by decide) (by decide) (by decide) (by decide)] using boundClean)
    (by simpa only [bank_other frame [] suffix word (some 17) (by decide) (by decide) (by decide) (by decide)] using scratchClean)
    (by simpa only [bank_other frame [] suffix word (some 9) (by decide) (by decide) (by decide) (by decide)] using saved)
  simp only [bank_word] at checking bound
  have trace := GuardedLink.success none Option.isNone reading checking (by simp [bank_counter])
  refine ⟨14*word.length+12+ticks,_,trace,?_⟩
  have identity : word.length*(4*registers+19)+6*registers+26=
      14*word.length+12+(word.length*(4*registers+5)+6*registers+14) := by ring
  rw [identity]
  omega

theorem read_immediate (frame : Port → List Bool) (word suffix rest : List Bool)
    (widthStored : frame (some 8)=List.replicate word.length true)
    (roleStored : frame (some 18)=false :: rest) :
    ∃ peak, Execution reader
      ⟨some reader.main,WordReader.bank frame [] (word++suffix) []⟩
      ⟨none,Function.update (Function.update (WordReader.bank frame [] suffix word) (some 18) rest) (some 1) []⟩
      (15*word.length+15) peak := by
  have reading := WidthReader.execution frame word suffix widthStored
  obtain ⟨peak,checking⟩ := immediate_execution (WordReader.bank frame [] suffix word) rest
    (by simpa only [bank_other frame [] suffix word (some 18) (by decide) (by decide) (by decide) (by decide)] using roleStored)
  simp only [bank_word] at checking
  have trace := GuardedLink.success none Option.isNone reading checking (by simp [bank_counter])
  have ticks : (14*word.length+12)+(word.length+3)=15*word.length+15 := by omega
  exact ⟨_,by simpa only [reader, ticks] using trace⟩

theorem read_short (frame : Port → List Bool) (missing : Nat) (input : List Bool)
    (widthStored : frame (some 8)=List.replicate (input.length+missing+1) true) :
    Execution reader ⟨some reader.main,WordReader.bank frame [] input []⟩
      ⟨none,WordReader.bank frame (false :: List.replicate missing true) [] input.reverse⟩
      (5*(input.length+missing+1)+3*input.length+10)
      ((input.length+missing+1)+input.length+ambientBits frame) := by
  have trace := GuardedLink.failure program none Option.isNone (WidthReader.short_execution frame missing input widthStored)
    (by simp [bank_counter])
  simpa only [reader, Nat.add_assoc, Nat.reduceAdd] using trace

theorem reader_resident : (∑ label, statementSize (tmStatement (reader.code label))) ≤ 576 := by
  simpa [reader, GuardedLink.program, WidthReader.program, WidthReader.counterMachine, StackFrames.relocate,
    StackCopy.program, WordReader.program, WordReader.cursorMachine, WordReader.reverseMachine,
    StackBlocks.reverseProgram, program, Label, RegisterRange.Label, WordBound.Label, WordBound.BodyLabel, link] using
      finiteTM_resident reader

end Controller.Complexity.OperandCheck
