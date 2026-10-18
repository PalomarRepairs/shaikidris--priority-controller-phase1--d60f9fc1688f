module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ColdInput
public import Controller.Complexity.StackCopy

@[expose] public section

/-! A word read copies the persistent width into its working counter by an
actual source-preserving program. The reader charges this setup on successful
and truncated input and retains the saved width for subsequent fields. -/
namespace Controller.Complexity.WidthReader
open StackMachine StackBlocks WordReader
open scoped BigOperators

def copyPorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 8) none (some 2) (by decide) (by decide) (by decide)

theorem copyPorts_apply (port : Option Bool) : copyPorts port =
    (match port with | none => some 8 | some false => none | some true => some 2) := rfl

theorem copy_storage (frame : Port → List Bool) (width : Nat) (source counter : List Bool)
    (stored : frame (some 8) = List.replicate width true) :
    StackFrames.embedStorage copyPorts (bank frame [] source [])
      (layout (List.replicate width true) counter []) = bank frame counter source [] := by
  funext target
  by_cases hc : target=none <;> by_cases hs : target=some 0 <;>
    by_cases hw : target=some 1 <;> by_cases ht : target=some 2 <;> by_cases hd : target=some 8 <;>
    simp_all [StackFrames.embedStorage, copyPorts_apply, bank, cursorFrame, cursorPorts_apply, layout]

theorem copy_frame_bits (frame : Port → List Bool) (width : Nat) (source : List Bool)
    (stored : frame (some 8) = List.replicate width true) :
    width+StackFrames.frameBits copyPorts (bank frame [] source []) = source.length+ambientBits frame := by
  have bound := StackFrames.live_embed copyPorts (bank frame [] source [])
    (⟨none,layout (List.replicate width true) [] []⟩ : State Bool Unit)
  simp only [StackFrames.embedState, copy_storage frame width source [] stored, bank_live,
    live_layout, List.length_nil, List.length_replicate, Nat.zero_add, Nat.add_zero] at bound
  exact bound.symm

def counterMachine := StackFrames.relocate copyPorts StackCopy.program
def program := link counterMachine WordReader.program

theorem counter_execution (frame : Port → List Bool) (width : Nat) (source : List Bool)
    (stored : frame (some 8) = List.replicate width true) :
    Execution counterMachine ⟨some counterMachine.main,bank frame [] source []⟩
      ⟨none,bank frame (List.replicate width true) source []⟩
      (5*width+4) (width+source.length+ambientBits frame) := by
  have trace := StackCopy.framed_execution copyPorts (bank frame [] source []) (List.replicate width true) []
  have bound := copy_frame_bits frame width source stored
  have peak : 2*width+0+StackFrames.frameBits copyPorts (bank frame [] source []) =
      width+source.length+ambientBits frame := by omega
  simpa only [counterMachine, StackFrames.relocate, StackFrames.embedState,
    List.append_nil, copy_storage frame width source _ stored, List.length_replicate, List.length_nil, peak] using trace

theorem execution (frame : Port → List Bool) (word suffix : List Bool)
    (stored : frame (some 8) = List.replicate word.length true) :
    Execution program ⟨some program.main,bank frame [] (word++suffix) []⟩
      ⟨none,bank frame [] suffix word⟩ (14*word.length+12)
      (word.length+(word++suffix).length+ambientBits frame) := by
  have trace := (counter_execution frame word.length (word++suffix) stored).link (WordReader.execution frame word suffix)
  have ticks : (5*word.length+4)+(9*word.length+8)=14*word.length+12 := by omega
  have peak : word.length+(word++suffix).length+ambientBits frame = 2*word.length+suffix.length+ambientBits frame := by
    rw [List.length_append]
    omega
  simpa only [program, ticks, peak, Nat.max_self] using trace

theorem short_execution (frame : Port → List Bool) (missing : Nat) (input : List Bool)
    (stored : frame (some 8) = List.replicate (input.length+missing+1) true) :
    Execution program ⟨some program.main,bank frame [] input []⟩
      ⟨none,bank frame (false :: List.replicate missing true) [] input.reverse⟩
      (5*(input.length+missing+1)+3*input.length+9)
      ((input.length+missing+1)+input.length+ambientBits frame) := by
  have trace := (counter_execution frame (input.length+missing+1) input stored).link
    (WordReader.short_execution frame missing input)
  have ticks : (5*(input.length+missing+1)+4)+(3*input.length+5) =
      5*(input.length+missing+1)+3*input.length+9 := by omega
  have peak : max ((input.length+missing+1)+input.length+ambientBits frame)
      (2*input.length+missing+1+ambientBits frame) = (input.length+missing+1)+input.length+ambientBits frame := by omega
  simpa only [program, ticks, peak] using trace

theorem total_execution (frame : Port → List Bool) (width : Nat) (input : List Bool)
    (stored : frame (some 8) = List.replicate width true) :
    ∃ final ticks, Execution program ⟨some program.main,bank frame [] input []⟩ final ticks
      (width+input.length+ambientBits frame) ∧ ticks ≤ 14*width+12 ∧
      final = if width ≤ input.length then ⟨none,bank frame [] (input.drop width) (input.take width)⟩
        else ⟨none,bank frame (false :: List.replicate (width-input.length-1) true) [] input.reverse⟩ := by
  by_cases enough : width ≤ input.length
  · have prefixLength : (input.take width).length=width := by simp only [List.length_take, Nat.min_eq_left enough]
    have trace := execution frame (input.take width) (input.drop width) (by simpa only [prefixLength] using stored)
    rw [List.take_append_drop, prefixLength] at trace
    exact ⟨_,_,trace,le_rfl,by simp only [ite_eq_left enough]⟩
  · let missing := width-input.length-1
    have full : width=input.length+missing+1 := by dsimp [missing]; omega
    have trace := short_execution frame missing input (by simpa only [← full] using stored)
    rw [← full] at trace
    exact ⟨_,_,trace,by omega,by simp only [ite_eq_right enough]; rfl⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 261 := by
  simpa [program, counterMachine, StackFrames.relocate, StackCopy.program, WordReader.program,
    WordReader.cursorMachine, WordReader.reverseMachine, GuardedLink.program, link, reverseProgram] using
      finiteTM_resident program

end Controller.Complexity.WidthReader
