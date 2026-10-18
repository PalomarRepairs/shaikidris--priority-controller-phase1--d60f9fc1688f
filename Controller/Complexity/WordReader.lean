module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordCursor
public import Controller.Complexity.GuardedLink

@[expose] public section

/-! Checked little-endian word reading in a fixed bank of 32 physical stacks.
The width counter, source stream, result word and scratch use fixed ports;
all other banks retain arbitrary data. Reversal runs only after successful
extraction. Truncated input halts with its error counter and skips reversal. -/
namespace Controller.Complexity.WordReader
open StackMachine StackBlocks
open scoped BigOperators

abbrev Port := Option (Fin 31)

def cursorPorts : Option Bool ↪ Port :=
  StackFrames.threePorts none (some 0) (some 1) (by decide) (by decide) (by decide)

def reversePorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 1) none (some 2) (by decide) (by decide) (by decide)

theorem cursorPorts_apply (port : Option Bool) : cursorPorts port =
    (match port with | none => none | some false => some 0 | some true => some 1) := rfl

theorem reversePorts_apply (port : Option Bool) : reversePorts port =
    (match port with | none => some 1 | some false => none | some true => some 2) := rfl

def cursorFrame (frame : Port → List Bool) : Port → List Bool := Function.update frame (some 2) []

def bank (frame : Port → List Bool) (counter source word : List Bool) : Port → List Bool :=
  StackFrames.embedStorage cursorPorts (cursorFrame frame) (layout counter source word)

def ambientBits (frame : Port → List Bool) : Nat := StackFrames.frameBits cursorPorts (cursorFrame frame)

theorem bank_counter (frame : Port → List Bool) (counter source word : List Bool) :
    bank frame counter source word none = counter := by
  simp [bank, StackFrames.embedStorage, cursorPorts_apply, layout]

theorem bank_source (frame : Port → List Bool) (counter source word : List Bool) :
    bank frame counter source word (some 0) = source := by
  simp [bank, StackFrames.embedStorage, cursorPorts_apply, layout]

theorem bank_word (frame : Port → List Bool) (counter source word : List Bool) :
    bank frame counter source word (some 1) = word := by
  simp [bank, StackFrames.embedStorage, cursorPorts_apply, layout]

theorem bank_scratch (frame : Port → List Bool) (counter source word : List Bool) :
    bank frame counter source word (some 2) = [] := by
  simp [bank, StackFrames.embedStorage, cursorPorts_apply, cursorFrame]

theorem bank_other (frame : Port → List Bool) (counter source word : List Bool) (target : Port)
    (notCounter : target ≠ none) (notSource : target ≠ some 0) (notWord : target ≠ some 1) (notScratch : target ≠ some 2) :
    bank frame counter source word target = frame target := by
  simp [bank, StackFrames.embedStorage, cursorPorts_apply, cursorFrame,
    notCounter, notSource, notWord, notScratch]

theorem bank_live (frame : Port → List Bool) (label : Option Q) (counter source word : List Bool) :
    live (⟨label,bank frame counter source word⟩ : State (Fin 31) Q) =
      counter.length+source.length+word.length+ambientBits frame := by
  have bound := StackFrames.live_embed cursorPorts (cursorFrame frame) (⟨label,layout counter source word⟩ : State Bool Q)
  simpa only [StackFrames.embedState, bank, ambientBits, live_layout] using bound

theorem reverse_storage (frame : Port → List Bool) (word source : List Bool) :
    StackFrames.embedStorage reversePorts (Function.update frame (some 0) source) (layout word [] []) =
      bank frame [] source word := by
  funext target
  by_cases h₀ : target=none <;> by_cases h₁ : target=some 0 <;>
    by_cases h₂ : target=some 1 <;> by_cases h₃ : target=some 2 <;>
    simp_all [StackFrames.embedStorage, reversePorts_apply, cursorPorts_apply,
      bank, cursorFrame, layout]

theorem reverse_frame_bits (frame : Port → List Bool) (source : List Bool) :
    StackFrames.frameBits reversePorts (Function.update frame (some 0) source) = source.length+ambientBits frame := by
  have bound := StackFrames.live_embed reversePorts (Function.update frame (some 0) source)
    (⟨none,layout [] [] []⟩ : State Bool Unit)
  simp only [StackFrames.embedState, reverse_storage, bank_live, live_layout,
    List.length_nil, Nat.zero_add, Nat.add_zero] at bound
  exact bound.symm

def cursorMachine := StackFrames.relocate cursorPorts WordCursor.program
def reverseMachine := StackFrames.relocate reversePorts StackBlocks.reverseProgram
def program := GuardedLink.program cursorMachine reverseMachine none Option.isNone

theorem cursorMachine_main : cursorMachine.main = 0 := rfl

theorem cursor_execution (frame : Port → List Bool) (word suffix : List Bool) :
    Execution cursorMachine
      ⟨some cursorMachine.main,bank frame (List.replicate word.length true) (word ++ suffix) []⟩
      ⟨none,bank frame [] suffix word.reverse⟩
      (3*word.length+2) (2*word.length+suffix.length+ambientBits frame) := by
  simp only [cursorMachine_main]
  have trace := WordCursor.framed_execution cursorPorts (cursorFrame frame) word suffix []
  simpa only [cursorMachine, StackFrames.relocate, StackFrames.embedState, WordCursor.state,
    bank, ambientBits, List.append_nil, List.length_nil, Nat.add_zero] using trace

theorem reverse_execution (frame : Port → List Bool) (word suffix : List Bool) :
    Execution reverseMachine ⟨some reverseMachine.main,bank frame [] suffix word.reverse⟩
      ⟨none,bank frame [] suffix word⟩ (6*word.length+6) (word.length+suffix.length+ambientBits frame) := by
  have trace := StackFrames.reversal reversePorts (Function.update frame (some 0) suffix) word.reverse
  simpa only [reverseMachine, StackFrames.relocate, initial_layout, terminal_layout,
    StackFrames.embedState, reverse_storage, reverse_frame_bits, List.length_reverse,
    List.reverse_reverse, Nat.add_assoc] using trace

theorem execution (frame : Port → List Bool) (word suffix : List Bool) :
    Execution program ⟨some program.main,bank frame (List.replicate word.length true) (word ++ suffix) []⟩
      ⟨none,bank frame [] suffix word⟩ (9*word.length+8) (2*word.length+suffix.length+ambientBits frame) := by
  have accepted : Option.isNone ((bank frame [] suffix word.reverse none).head?) = true := by simp [bank_counter]
  have trace := GuardedLink.success none Option.isNone (cursor_execution frame word suffix)
    (reverse_execution frame word suffix) accepted
  have ticks : (3*word.length+2)+(6*word.length+6)=9*word.length+8 := by omega
  have peak : max (2*word.length+suffix.length+ambientBits frame) (word.length+suffix.length+ambientBits frame) =
      2*word.length+suffix.length+ambientBits frame := by omega
  simpa only [program, ticks, peak] using trace

theorem short_execution (frame : Port → List Bool) (missing : Nat) (input : List Bool) :
    Execution program ⟨some program.main,bank frame (List.replicate (input.length+missing+1) true) input []⟩
      ⟨none,bank frame (false :: List.replicate missing true) [] input.reverse⟩
      (3*input.length+5) (2*input.length+missing+1+ambientBits frame) := by
  have first : Execution cursorMachine
      ⟨some cursorMachine.main,bank frame (List.replicate (input.length+missing+1) true) input []⟩
      ⟨none,bank frame (false :: List.replicate missing true) [] input.reverse⟩
      (3*input.length+4) (2*input.length+missing+1+ambientBits frame) := by
    simp only [cursorMachine_main]
    simpa only [cursorMachine, StackFrames.relocate, StackFrames.embedState, WordCursor.state,
      bank, ambientBits, List.append_nil, List.length_nil, Nat.add_zero] using
      WordCursor.framed_short_execution cursorPorts (cursorFrame frame) missing input []
  have rejected : Option.isNone ((bank frame (false :: List.replicate missing true) [] input.reverse none).head?) = false := by
    simp [bank_counter]
  have trace := GuardedLink.failure reverseMachine none Option.isNone first rejected
  have ticks : (3*input.length+4)+1=3*input.length+5 := by omega
  simpa only [program, ticks] using trace

theorem encoded_execution (frame : Port → List Bool) (width value : Nat) (suffix : List Bool) :
    Execution program ⟨some program.main,bank frame (List.replicate width true) (Encoding.bits width value ++ suffix) []⟩
      ⟨none,bank frame [] suffix (Encoding.bits width value)⟩
      (9*width+8) (2*width+suffix.length+ambientBits frame) := by
  simpa only [Encoding.bits_length] using execution frame (Encoding.bits width value) suffix

theorem decoded_word (width value : Nat) : Encoding.decodeWord width (Encoding.bits width value) =
    some (Controller.Cost.word width value) := by
  simp [Encoding.decodeWord, Encoding.bits_length, WordArithmetic.value_bits_mod, Controller.Cost.word]

theorem execution_decodes (frame : Port → List Bool) (width value : Nat) (suffix : List Bool) :
    ∃ final, Execution program
      ⟨some program.main,bank frame (List.replicate width true) (Encoding.bits width value ++ suffix) []⟩ final
      (9*width+8) (2*width+suffix.length+ambientBits frame) ∧
      Encoding.decodeWord width (final.stk (some 1)) = some (Controller.Cost.word width value) ∧
      final.stk (some 0) = suffix ∧ final.stk none = [] ∧ final.stk (some 2) = [] := by
  refine ⟨⟨none,bank frame [] suffix (Encoding.bits width value)⟩,encoded_execution frame width value suffix,?_,?_,?_,?_⟩
  · simpa only [bank_word] using decoded_word width value
  · exact bank_source frame [] suffix (Encoding.bits width value)
  · exact bank_counter frame [] suffix (Encoding.bits width value)
  · exact bank_scratch frame [] suffix (Encoding.bits width value)

theorem total_execution (frame : Port → List Bool) (width : Nat) (input : List Bool) :
    ∃ final ticks, Execution program ⟨some program.main,bank frame (List.replicate width true) input []⟩ final ticks
      (width+input.length+ambientBits frame) ∧ ticks ≤ 9*width+8 ∧
      final = if width ≤ input.length then ⟨none,bank frame [] (input.drop width) (input.take width)⟩
        else ⟨none,bank frame (false :: List.replicate (width-input.length-1) true) [] input.reverse⟩ := by
  by_cases enough : width ≤ input.length
  · have prefixLength : (input.take width).length = width := by simp only [List.length_take, Nat.min_eq_left enough]
    have trace := execution frame (input.take width) (input.drop width)
    rw [List.take_append_drop, prefixLength] at trace
    have peak : 2*width+(input.drop width).length+ambientBits frame = width+input.length+ambientBits frame := by
      simp only [List.length_drop]
      omega
    rw [peak] at trace
    exact ⟨_,_,trace,le_rfl,by simp only [ite_eq_left enough]⟩
  · let missing := width-input.length-1
    have full : width=input.length+missing+1 := by dsimp [missing]; omega
    have trace := short_execution frame missing input
    rw [← full] at trace
    have peak : 2*input.length+missing+1+ambientBits frame = width+input.length+ambientBits frame := by omega
    rw [peak] at trace
    exact ⟨_,_,trace,by omega,by simp only [ite_eq_right enough]; rfl⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 171 := by
  simpa [program, cursorMachine, reverseMachine, StackFrames.relocate, GuardedLink.program, StackBlocks.reverseProgram] using
    finiteTM_resident program

end Controller.Complexity.WordReader
