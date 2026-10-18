module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ColdInput

@[expose] public section

/-! The instruction tag has constant width four, independent of the saved
machine-word width. Its counter is built by charged pushes. Successful reads
save the tag in most-significant-first order in port 13; short tags preserve
their error data and skip publication. -/
namespace Controller.Complexity.OpcodeReader
open StackMachine StackBlocks WordReader
open scoped BigOperators

def seed : Program (Fin 31) (Fin 5) where
  main := 0
  code label := if h : label.val < 4 then .push none true ⟨label.val+1,by omega⟩ else .halt

theorem counter_update (frame : Port → List Bool) (counter source word : List Bool) (replacement : List Bool) :
    Function.update (bank frame counter source word) none replacement = bank frame replacement source word := by
  funext target
  by_cases hc : target=none <;> by_cases hs : target=some 0 <;>
    by_cases hw : target=some 1 <;> by_cases ht : target=some 2 <;>
    simp_all [bank, cursorFrame, cursorPorts_apply, StackFrames.embedStorage, layout]

theorem seed_step (label : Fin 4) (frame : Port → List Bool) (counter source : List Bool) :
    step seed ⟨some label.castSucc,bank frame counter source []⟩ =
      some ⟨some label.succ,bank frame (true :: counter) source []⟩ := by
  simp [step, seed, instructionStep, label.isLt, bank_counter, counter_update]
  rfl

theorem seed_halt (frame : Port → List Bool) (source : List Bool) :
    step seed ⟨some 4,bank frame (List.replicate 4 true) source []⟩ =
      some ⟨none,bank frame (List.replicate 4 true) source []⟩ := rfl

theorem seed_execution (frame : Port → List Bool) (input : List Bool) :
    ∃ peak, Execution seed ⟨some seed.main,bank frame [] input []⟩
      ⟨none,bank frame (List.replicate 4 true) input []⟩ 5 peak := by
  have final := Execution.refl (program := seed) ⟨none,bank frame (List.replicate 4 true) input []⟩
  have last := Execution.cons (seed_halt frame input) final
  have three := Execution.cons (seed_step 3 frame (List.replicate 3 true) input) last
  have two := Execution.cons (seed_step 2 frame (List.replicate 2 true) input) three
  have one := Execution.cons (seed_step 1 frame (List.replicate 1 true) input) two
  have zero := Execution.cons (seed_step 0 frame [] input) one
  exact ⟨_,zero⟩

def readMachine := link seed WordReader.program

theorem read_execution (frame : Port → List Bool) (tag suffix : List Bool) (width : tag.length=4) :
    ∃ peak, Execution readMachine ⟨some readMachine.main,bank frame [] (tag++suffix) []⟩
      ⟨none,bank frame [] suffix tag⟩ 49 peak := by
  obtain ⟨seedPeak,seeding⟩ := seed_execution frame (tag++suffix)
  have reading := WordReader.execution frame tag suffix
  rw [width] at reading
  exact ⟨_,seeding.link reading⟩

theorem read_short (frame : Port → List Bool) (input : List Bool) (short : input.length < 4) :
    ∃ peak, Execution readMachine ⟨some readMachine.main,bank frame [] input []⟩
      ⟨none,bank frame (false :: List.replicate (3-input.length) true) [] input.reverse⟩ (3*input.length+10) peak := by
  obtain ⟨seedPeak,seeding⟩ := seed_execution frame input
  have width : input.length+(3-input.length)+1=4 := by omega
  have reading := WordReader.short_execution frame (3-input.length) input
  rw [width] at reading
  have trace := seeding.link reading
  have ticks : 5+(3*input.length+5)=3*input.length+10 := by omega
  exact ⟨_,by simpa only [readMachine, ticks] using trace⟩

theorem move_storage (frame : Port → List Bool) (source word tag : List Bool) :
    storage (bank frame [] source []) (some 1) (some 13) word tag =
      bank (Function.update frame (some 13) tag) [] source word := by
  funext target
  by_cases hc : target=none <;> by_cases hs : target=some 0 <;>
    by_cases hw : target=some 1 <;> by_cases ht : target=some 2 <;> by_cases hd : target=some 13 <;>
    simp_all [storage, bank, cursorFrame, cursorPorts_apply, StackFrames.embedStorage, layout]

def saveMachine := transfer (K := Fin 31) (some 1) (some 13)
def program := GuardedLink.program readMachine saveMachine none Option.isNone

theorem save_execution (frame : Port → List Bool) (source tag : List Bool) (empty : frame (some 13)=[]) :
    ∃ peak, Execution saveMachine ⟨some saveMachine.main,bank frame [] source tag⟩
      ⟨none,bank (Function.update frame (some 13) tag.reverse) [] source []⟩ (2*tag.length+2) peak := by
  change ∃ peak, Execution saveMachine ⟨some 0,bank frame [] source tag⟩ _ _ peak
  have trace := transfer_execution (bank frame [] source []) (source := some 1) (destination := some 13) (by decide) tag []
  simpa only [saveMachine, state, move_storage, List.append_nil, ColdInput.update_empty frame (some 13) empty] using Exists.intro _ trace

theorem execution (frame : Port → List Bool) (tag suffix : List Bool) (width : tag.length=4) (empty : frame (some 13)=[]) :
    ∃ peak, Execution program ⟨some program.main,bank frame [] (tag++suffix) []⟩
      ⟨none,bank (Function.update frame (some 13) tag.reverse) [] suffix []⟩ 59 peak := by
  obtain ⟨readPeak,reading⟩ := read_execution frame tag suffix width
  obtain ⟨savePeak,saving⟩ := save_execution frame suffix tag empty
  rw [width] at saving
  have accepted : Option.isNone ((bank frame [] suffix tag none).head?) = true := by simp [bank_counter]
  exact ⟨_,GuardedLink.success none Option.isNone reading saving accepted⟩

theorem short_execution (frame : Port → List Bool) (input : List Bool) (short : input.length < 4) :
    ∃ peak, Execution program ⟨some program.main,bank frame [] input []⟩
      ⟨none,bank frame (false :: List.replicate (3-input.length) true) [] input.reverse⟩ (3*input.length+11) peak := by
  obtain ⟨readPeak,reading⟩ := read_short frame input short
  have rejected : Option.isNone ((bank frame (false :: List.replicate (3-input.length) true) [] input.reverse none).head?) = false := by
    simp [bank_counter]
  have trace := GuardedLink.failure saveMachine none Option.isNone reading rejected
  have ticks : (3*input.length+10)+1=3*input.length+11 := by omega
  exact ⟨_,by simpa only [program, ticks] using trace⟩

theorem encoded_execution (frame : Port → List Bool) (tag : Fin 16) (suffix : List Bool) (empty : frame (some 13)=[]) :
    ∃ peak, Execution program ⟨some program.main,bank frame [] (Encoding.bits 4 tag.val++suffix) []⟩
      ⟨none,bank (Function.update frame (some 13) (Encoding.bits 4 tag.val).reverse) [] suffix []⟩ 59 peak :=
  execution frame _ suffix (Encoding.bits_length 4 tag.val) empty

theorem bank_tag (frame : Port → List Bool) (counter source word tag : List Bool) :
    bank (Function.update frame (some 13) tag) counter source word (some 13)=tag := by
  rw [bank_other _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
  simp

theorem execution_decodes (frame : Port → List Bool) (tag : Fin 16) (suffix : List Bool) (empty : frame (some 13)=[]) :
    ∃ final peak, Execution program ⟨some program.main,bank frame [] (Encoding.bits 4 tag.val++suffix) []⟩ final 59 peak ∧
      Encoding.decodeWord 4 (final.stk (some 13)).reverse=some tag ∧ final.stk (some 0)=suffix := by
  obtain ⟨peak,trace⟩ := encoded_execution frame tag suffix empty
  refine ⟨_,peak,trace,?_,?_⟩
  · have parsed := (Encoding.wordEncoding 4).decode_encode tag
    change Encoding.decodeWord 4 (Encoding.bits 4 tag.val)=some tag at parsed
    simpa only [bank_tag, List.reverse_reverse] using parsed
  · exact bank_source (Function.update frame (some 13) (Encoding.bits 4 tag.val).reverse) [] suffix []

def result (frame : Port → List Bool) (input : List Bool) : Port → List Bool :=
  if 4 ≤ input.length then bank (Function.update frame (some 13) (input.take 4).reverse) [] (input.drop 4) []
  else bank frame (false :: List.replicate (3-input.length) true) [] input.reverse

theorem total_execution (frame : Port → List Bool) (input : List Bool) (empty : frame (some 13)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] input []⟩ ⟨none,result frame input⟩ ticks peak ∧
      ticks ≤ 59 ∧ peak ≤ input.length+ambientBits frame+59 := by
  by_cases enough : 4 ≤ input.length
  · have width : (input.take 4).length=4 := by simp only [List.length_take, Nat.min_eq_left enough]
    obtain ⟨peak,trace⟩ := execution frame (input.take 4) (input.drop 4) width empty
    rw [List.take_append_drop] at trace
    have space := trace.peak_le
    simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
    exact ⟨59,peak,by simpa only [result, ite_eq_left enough] using trace,le_rfl,space⟩
  · obtain ⟨peak,trace⟩ := short_execution frame input (by omega)
    have space := trace.peak_le
    simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
    exact ⟨_,peak,by simpa only [result, ite_eq_right enough] using trace,by omega,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 261 := by
  simpa [program, readMachine, saveMachine, seed, GuardedLink.program, WordReader.program,
    WordReader.cursorMachine, WordReader.reverseMachine, StackFrames.relocate, reverseProgram, link] using finiteTM_resident program

end Controller.Complexity.OpcodeReader
