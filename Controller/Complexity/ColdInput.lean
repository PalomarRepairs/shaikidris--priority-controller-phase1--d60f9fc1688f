module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordReader
public import Controller.Complexity.HeaderParser
public import Controller.Complexity.MachineInput

@[expose] public section

/-! Cold input placement and guarded global-header parsing in the fixed VM
bank. All input movement, order restoration and saved unary counts are charged
to literal binary-stack transitions. Unselected banks retain their data. -/
namespace Controller.Complexity.ColdInput
open StackMachine StackBlocks WordReader
open scoped BigOperators

def headerPorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 0) none (some 2) (by decide) (by decide) (by decide)

theorem headerPorts_apply (port : Option Bool) : headerPorts port =
    (match port with | none => some 0 | some false => none | some true => some 2) := rfl

def headerFrame (frame : Port → List Bool) (word : List Bool) := Function.update frame (some 1) word

theorem header_storage (frame : Port → List Bool) (source counter word : List Bool) :
    StackFrames.embedStorage headerPorts (headerFrame frame word) (layout source counter []) =
      bank frame counter source word := by
  funext target
  by_cases h₀ : target=none <;> by_cases h₁ : target=some 0 <;>
    by_cases h₂ : target=some 1 <;> by_cases h₃ : target=some 2 <;>
    simp_all [StackFrames.embedStorage, headerPorts_apply, headerFrame,
      bank, cursorFrame, cursorPorts_apply, layout]

theorem header_frame_bits (frame : Port → List Bool) (word : List Bool) :
    StackFrames.frameBits headerPorts (headerFrame frame word) = word.length+ambientBits frame := by
  have bound := StackFrames.live_embed headerPorts (headerFrame frame word)
    (⟨none,layout [] [] []⟩ : State Bool Unit)
  simp only [StackFrames.embedState, header_storage, bank_live, live_layout,
    List.length_nil, Nat.zero_add, Nat.add_zero] at bound
  exact bound.symm

theorem move_storage (frame : Port → List Bool) (counter source word : List Bool) :
    storage (bank frame [] [] word) none (some 0) counter source = bank frame counter source word := by
  funext target
  by_cases h₀ : target=none <;> by_cases h₁ : target=some 0 <;>
    by_cases h₂ : target=some 1 <;> by_cases h₃ : target=some 2 <;>
    simp_all [storage, bank, cursorFrame, cursorPorts_apply, StackFrames.embedStorage, layout]

def moveMachine := transfer (K := Fin 31) none (some 0)
def restoreMachine := StackFrames.relocate headerPorts reverseProgram
def bootstrap := link moveMachine restoreMachine

theorem move_execution (frame : Port → List Bool) (input : List Bool) :
    Execution moveMachine ⟨some moveMachine.main,bank frame input [] []⟩
      ⟨none,bank frame [] input.reverse []⟩ (2*input.length+2) (input.length+ambientBits frame) := by
  have trace := transfer_execution (bank frame [] [] []) (source := none) (destination := some 0) (by decide) input []
  simpa only [moveMachine, transfer, state, move_storage, bank_live, List.append_nil,
    List.length_nil, Nat.add_zero] using trace

theorem restore_execution (frame : Port → List Bool) (input : List Bool) :
    Execution restoreMachine ⟨some restoreMachine.main,bank frame [] input []⟩
      ⟨none,bank frame [] input.reverse []⟩ (6*input.length+6) (input.length+ambientBits frame) := by
  have trace := StackFrames.reversal headerPorts (headerFrame frame []) input
  simpa only [restoreMachine, StackFrames.relocate, initial_layout, terminal_layout,
    StackFrames.embedState, header_storage, header_frame_bits, List.length_nil, Nat.zero_add] using trace

theorem bootstrap_execution (frame : Port → List Bool) (input : List Bool) :
    Execution bootstrap ⟨some bootstrap.main,bank frame input [] []⟩
      ⟨none,bank frame [] input []⟩ (8*input.length+8) (input.length+ambientBits frame) := by
  have trace := (move_execution frame input).link (restore_execution frame input.reverse)
  have ticks : (2*input.length+2)+(6*input.length+6)=8*input.length+8 := by omega
  simpa only [bootstrap, ticks, List.length_reverse, List.reverse_reverse, Nat.max_self] using trace

def emptyFrame : Port → List Bool := fun _ => []

theorem empty_ambient : ambientBits emptyFrame = 0 := by
  simp [ambientBits, StackFrames.frameBits, StackFrames.embedStorage, cursorFrame,
    cursorPorts_apply, emptyFrame, Function.update_apply]

theorem initial_bank (program : Program (Fin 31) Q) (input : List Bool) :
    initial program input = (⟨some program.main,bank emptyFrame input [] []⟩ : State (Fin 31) Q) := by
  unfold initial
  congr 1
  funext target
  by_cases h₀ : target=none <;> by_cases h₁ : target=some 0 <;>
    by_cases h₂ : target=some 1 <;> by_cases h₃ : target=some 2 <;>
    simp_all [bank, cursorFrame, cursorPorts_apply, StackFrames.embedStorage, layout, emptyFrame]
  cases target <;> simp_all

theorem cold_bootstrap (input : List Bool) :
    Execution bootstrap (initial bootstrap input) ⟨none,bank emptyFrame [] input []⟩
      (8*input.length+8) input.length := by
  rw [initial_bank]
  simpa only [empty_ambient, Nat.add_zero] using bootstrap_execution emptyFrame input

def headerMachine := StackFrames.relocate headerPorts HeaderParser.program

theorem headerMachine_main : headerMachine.main = 0 := rfl

theorem header_execution (frame : Port → List Bool) (count : Nat) (payload word : List Bool) :
    Execution headerMachine ⟨some headerMachine.main,bank frame [] (Encoding.frameCount count payload) word⟩
      ⟨none,bank frame (List.replicate count true) payload word⟩
      (2*count+2) (count+1+payload.length+word.length+ambientBits frame) := by
  rw [headerMachine_main]
  have trace := HeaderParser.framed_execution headerPorts (headerFrame frame word) count payload [] []
  simpa only [headerMachine, StackFrames.relocate, StackFrames.embedState, HeaderParser.state,
    header_storage, header_frame_bits, List.append_nil, List.length_nil, Nat.add_zero, Nat.add_assoc] using trace

theorem header_eof (frame : Port → List Bool) (count : Nat) (word : List Bool) :
    Execution headerMachine ⟨some headerMachine.main,bank frame [] (List.replicate count true) word⟩
      ⟨none,bank frame (false :: List.replicate count true) [] word⟩
      (2*count+3) (count+word.length+ambientBits frame+1) := by
  rw [headerMachine_main]
  have trace := StackFrames.execution headerPorts (headerFrame frame word) (HeaderParser.eof_execution count [] [])
  simpa only [headerMachine, StackFrames.relocate, StackFrames.embedState, HeaderParser.state,
    header_storage, header_frame_bits, List.append_nil, List.length_nil, Nat.add_zero, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using trace

theorem bank_saved (frame : Port → List Bool) (slot : Fin 31)
    (h₀ : slot ≠ 0) (h₁ : slot ≠ 1) (h₂ : slot ≠ 2) (saved counter source word : List Bool) :
    bank (Function.update frame (some slot) saved) counter source word =
      Function.update (bank frame counter source word) (some slot) saved := by
  funext target
  by_cases hc : target=none <;> by_cases hs : target=some 0 <;>
    by_cases hw : target=some 1 <;> by_cases ht : target=some 2 <;> by_cases hd : target=some slot <;>
    simp_all [bank, cursorFrame, cursorPorts_apply, StackFrames.embedStorage, layout]

theorem ambient_saved (frame : Port → List Bool) (slot : Fin 31)
    (h₀ : slot ≠ 0) (h₁ : slot ≠ 1) (h₂ : slot ≠ 2) (saved : List Bool)
    (empty : frame (some slot) = []) :
    ambientBits (Function.update frame (some slot) saved) = ambientBits frame+saved.length := by
  have bound := live_update (⟨none,bank frame [] [] []⟩ : State (Fin 31) Unit) none (some slot) saved
  rw [← bank_saved frame slot h₀ h₁ h₂ saved [] [] []] at bound
  simp only [bank_live, List.length_nil, Nat.zero_add,
    bank_other frame [] [] [] (some slot) (by simp) (by simpa) (by simpa) (by simpa),
    empty, Nat.add_zero] at bound
  exact bound

theorem save_storage (frame : Port → List Bool) (slot : Fin 31)
    (h₀ : slot ≠ 0) (h₁ : slot ≠ 1) (h₂ : slot ≠ 2) (counter saved source word : List Bool) :
    storage (bank frame [] source word) none (some slot) counter saved =
      bank (Function.update frame (some slot) saved) counter source word := by
  rw [bank_saved frame slot h₀ h₁ h₂]
  unfold storage
  congr 1
  funext target
  by_cases hc : target=none <;> by_cases hs : target=some 0 <;>
    by_cases hw : target=some 1 <;> by_cases ht : target=some 2 <;>
    simp_all [bank, cursorFrame, cursorPorts_apply, StackFrames.embedStorage, layout]

theorem update_empty (frame : Port → List Bool) (slot : Port) (empty : frame slot = []) :
    Function.update frame slot [] = frame := by
  funext target
  by_cases same : target=slot <;> simp_all

theorem save_execution (frame : Port → List Bool) (slot : Fin 31)
    (h₀ : slot ≠ 0) (h₁ : slot ≠ 1) (h₂ : slot ≠ 2) (counter source word : List Bool)
    (empty : frame (some slot) = []) :
    Execution (transfer none (some slot)) ⟨some 0,bank frame counter source word⟩
      ⟨none,bank (Function.update frame (some slot) counter.reverse) [] source word⟩
      (2*counter.length+2) (counter.length+source.length+word.length+ambientBits frame) := by
  have trace := transfer_execution (bank frame [] source word) (source := none)
    (destination := some slot) (by simp) counter []
  simpa only [state, save_storage frame slot h₀ h₁ h₂, update_empty frame (some slot) empty,
    bank_live, List.append_nil] using trace

def readSave (slot : Fin 31) :=
  GuardedLink.program headerMachine (transfer none (some slot)) none HeaderParser.acceptCounter

theorem read_save_execution (frame : Port → List Bool) (slot : Fin 31)
    (h₀ : slot ≠ 0) (h₁ : slot ≠ 1) (h₂ : slot ≠ 2) (count : Nat) (payload word : List Bool)
    (empty : frame (some slot) = []) :
    Execution (readSave slot) ⟨some (readSave slot).main,bank frame [] (Encoding.frameCount count payload) word⟩
      ⟨none,bank (Function.update frame (some slot) (List.replicate count true)) [] payload word⟩
      (4*count+4) (count+1+payload.length+word.length+ambientBits frame) := by
  have saving := save_execution frame slot h₀ h₁ h₂ (List.replicate count true) payload word empty
  simp only [List.length_replicate, List.reverse_replicate] at saving
  have accepted : HeaderParser.acceptCounter ((bank frame (List.replicate count true) payload word none).head?) = true := by
    rw [bank_counter]
    exact HeaderParser.accept_success count
  have trace := GuardedLink.success none HeaderParser.acceptCounter (header_execution frame count payload word) saving accepted
  have ticks : (2*count+2)+(2*count+2)=4*count+4 := by omega
  have peak : max (count+1+payload.length+word.length+ambientBits frame)
      (count+payload.length+word.length+ambientBits frame) = count+1+payload.length+word.length+ambientBits frame := by omega
  simpa only [readSave, ticks, peak] using trace

theorem read_save_eof (frame : Port → List Bool) (slot : Fin 31) (count : Nat) (word : List Bool) :
    Execution (readSave slot) ⟨some (readSave slot).main,bank frame [] (List.replicate count true) word⟩
      ⟨none,bank frame (false :: List.replicate count true) [] word⟩
      (2*count+4) (count+word.length+ambientBits frame+1) := by
  have rejected : HeaderParser.acceptCounter ((bank frame (false :: List.replicate count true) [] word none).head?) = false := by
    simp [bank_counter, HeaderParser.acceptCounter]
  have trace := GuardedLink.failure (transfer none (some slot)) none HeaderParser.acceptCounter (header_eof frame count word) rejected
  simpa only [readSave, Nat.add_assoc] using trace

def headers := GuardedLink.program (readSave 8) (readSave 9) none Option.isNone
def setup := link bootstrap headers

def savedFrame (frame : Port → List Bool) (width registers : Nat) : Port → List Bool :=
  Function.update (Function.update frame (some 8) (List.replicate width true))
    (some 9) (List.replicate registers true)

theorem headers_execution (frame : Port → List Bool) (width registers : Nat) (payload word : List Bool)
    (widthEmpty : frame (some 8) = []) (registersEmpty : frame (some 9) = []) :
    Execution headers ⟨some headers.main,bank frame [] (MachineInput.envelope width registers payload) word⟩
      ⟨none,bank (savedFrame frame width registers) [] payload word⟩
      (4*width+4*registers+8) ((MachineInput.envelope width registers payload).length+word.length+ambientBits frame) := by
  let widthFrame := Function.update frame (some 8) (List.replicate width true)
  have first := read_save_execution frame 8 (by decide) (by decide) (by decide) width
    (Encoding.frameCount registers payload) word widthEmpty
  have second := read_save_execution widthFrame 9 (by decide) (by decide) (by decide) registers payload word
    (by simpa [widthFrame] using registersEmpty)
  have accepted : Option.isNone ((bank widthFrame [] (Encoding.frameCount registers payload) word none).head?) = true := by
    simp [bank_counter]
  have trace := GuardedLink.success none Option.isNone first second accepted
  have widthBits : ambientBits widthFrame = ambientBits frame+width := by
    simpa only [widthFrame, List.length_replicate] using
      ambient_saved frame 8 (by decide) (by decide) (by decide) (List.replicate width true) widthEmpty
  have ticks : (4*width+4)+(4*registers+4)=4*width+4*registers+8 := by omega
  have peak : max (width+1+(Encoding.frameCount registers payload).length+word.length+ambientBits frame)
      (registers+1+payload.length+word.length+ambientBits widthFrame) =
      (MachineInput.envelope width registers payload).length+word.length+ambientBits frame := by
    rw [widthBits, MachineInput.envelope_length]
    simp only [Encoding.frameCount, List.length_append, List.length_replicate, List.length_cons]
    omega
  simpa only [headers, MachineInput.envelope, savedFrame, widthFrame, ticks, peak] using trace

theorem headers_first_eof (frame : Port → List Bool) (count : Nat) (word : List Bool) :
    Execution headers ⟨some headers.main,bank frame [] (List.replicate count true) word⟩
      ⟨none,bank frame (false :: List.replicate count true) [] word⟩
      (2*count+5) (count+word.length+ambientBits frame+1) := by
  have rejected : Option.isNone ((bank frame (false :: List.replicate count true) [] word none).head?) = false := by
    simp [bank_counter]
  have trace := GuardedLink.failure (readSave 9) none Option.isNone (read_save_eof frame 8 count word) rejected
  simpa only [headers, Nat.add_assoc] using trace

theorem headers_second_eof (frame : Port → List Bool) (width count : Nat) (word : List Bool)
    (widthEmpty : frame (some 8) = []) :
    Execution headers ⟨some headers.main,bank frame [] (Encoding.frameCount width (List.replicate count true)) word⟩
      ⟨none,bank (Function.update frame (some 8) (List.replicate width true))
        (false :: List.replicate count true) [] word⟩
      (4*width+2*count+8) (width+count+word.length+ambientBits frame+1) := by
  let widthFrame := Function.update frame (some 8) (List.replicate width true)
  have first := read_save_execution frame 8 (by decide) (by decide) (by decide) width
    (List.replicate count true) word widthEmpty
  have second := read_save_eof widthFrame 9 count word
  have accepted : Option.isNone ((bank widthFrame [] (List.replicate count true) word none).head?) = true := by
    simp [bank_counter]
  have trace := GuardedLink.success none Option.isNone first second accepted
  have widthBits : ambientBits widthFrame = ambientBits frame+width := by
    simpa only [widthFrame, List.length_replicate] using
      ambient_saved frame 8 (by decide) (by decide) (by decide) (List.replicate width true) widthEmpty
  have ticks : (4*width+4)+(2*count+4)=4*width+2*count+8 := by omega
  have peak : max (width+1+(List.replicate count true).length+word.length+ambientBits frame)
      (count+word.length+ambientBits widthFrame+1) = width+count+word.length+ambientBits frame+1 := by
    rw [widthBits, List.length_replicate]
    omega
  simpa only [headers, widthFrame, ticks, peak] using trace

theorem setup_execution (width registers : Nat) (payload : List Bool) :
    Execution setup (initial setup (MachineInput.envelope width registers payload))
      ⟨none,bank (savedFrame emptyFrame width registers) [] payload []⟩
      (8*(MachineInput.envelope width registers payload).length+4*width+4*registers+16)
      (MachineInput.envelope width registers payload).length := by
  have first := bootstrap_execution emptyFrame (MachineInput.envelope width registers payload)
  have second := headers_execution emptyFrame width registers payload [] rfl rfl
  have trace := first.link second
  rw [initial_bank]
  have ticks : (8*(MachineInput.envelope width registers payload).length+8)+(4*width+4*registers+8) =
      8*(MachineInput.envelope width registers payload).length+4*width+4*registers+16 := by omega
  simpa only [setup, empty_ambient, List.length_nil, Nat.add_zero, ticks, Nat.max_self] using trace

theorem setup_image (image : MachineInput.Image) :
    Execution setup (initial setup (MachineInput.encode image))
      ⟨none,bank (savedFrame emptyFrame image.width image.registers) []
        (InstructionCodec.encodeProgram image.registerBound image.program ++ MachineBridge.encodeState image.state) []⟩
      (8*(MachineInput.encode image).length+4*image.width+4*image.registers+16)
      (MachineInput.encode image).length :=
  setup_execution image.width image.registers _

theorem setup_first_eof (count : Nat) :
    Execution setup (initial setup (List.replicate count true))
      ⟨none,bank emptyFrame (false :: List.replicate count true) [] []⟩
      (10*count+13) (count+1) := by
  have trace := (bootstrap_execution emptyFrame (List.replicate count true)).link
    (headers_first_eof emptyFrame count [])
  rw [initial_bank]
  have ticks : (8*count+8)+(2*count+5)=10*count+13 := by omega
  have peak : max count (count+1)=count+1 := by omega
  simpa only [setup, List.length_replicate, List.length_nil, Nat.add_zero, empty_ambient,
    ticks, peak] using trace

theorem setup_second_eof (width count : Nat) :
    Execution setup (initial setup (Encoding.frameCount width (List.replicate count true)))
      ⟨none,bank (Function.update emptyFrame (some 8) (List.replicate width true))
        (false :: List.replicate count true) [] []⟩
      (8*(width+count+1)+4*width+2*count+16) (width+count+1) := by
  have trace := (bootstrap_execution emptyFrame (Encoding.frameCount width (List.replicate count true))).link
    (headers_second_eof emptyFrame width count [] rfl)
  rw [initial_bank]
  have length : (Encoding.frameCount width (List.replicate count true)).length = width+count+1 := by
    simp only [Encoding.frameCount, List.length_append, List.length_replicate, List.length_cons]
    omega
  have ticks : (8*(width+count+1)+8)+(4*width+2*count+8)=8*(width+count+1)+4*width+2*count+16 := by omega
  simpa only [setup, length, List.length_nil, Nat.add_zero, empty_ambient, ticks, Nat.max_self] using trace

def setupResult (input : List Bool) : Port → List Bool :=
  match Encoding.readCount input with
  | none => bank emptyFrame (false :: List.replicate input.length true) [] []
  | some (width,rest) => match Encoding.readCount rest with
    | none => bank (Function.update emptyFrame (some 8) (List.replicate width true))
        (false :: List.replicate rest.length true) [] []
    | some (registers,payload) => bank (savedFrame emptyFrame width registers) [] payload []

theorem total_setup (input : List Bool) :
    ∃ ticks peak, Execution setup (initial setup input) ⟨none,setupResult input⟩ ticks peak ∧
      ticks ≤ 12*input.length+16 ∧ peak ≤ input.length+1 := by
  cases first : Encoding.readCount input with
  | none =>
    have shape := HeaderParser.readCount_none first
    have trace := setup_first_eof input.length
    have start := congrArg (initial setup) shape
    rw [← start] at trace
    exact ⟨_,_,by simpa only [setupResult, first] using trace,by omega,le_rfl⟩
  | some pair =>
    rcases pair with ⟨width,rest⟩
    have outerShape := HeaderParser.readCount_sound first
    cases second : Encoding.readCount rest with
    | none =>
      have innerShape := HeaderParser.readCount_none second
      have shape : input = Encoding.frameCount width (List.replicate rest.length true) :=
        outerShape.trans (congrArg (Encoding.frameCount width) innerShape)
      have length : input.length=width+rest.length+1 := by
        rw [shape]
        simp only [Encoding.frameCount, List.length_append, List.length_replicate, List.length_cons]
        omega
      have trace := setup_second_eof width rest.length
      rw [← shape] at trace
      exact ⟨_,_,by simpa only [setupResult, first, second] using trace,by omega,by omega⟩
    | some pair =>
      rcases pair with ⟨registers,payload⟩
      have innerShape := HeaderParser.readCount_sound second
      have shape : input = MachineInput.envelope width registers payload := by rw [outerShape,innerShape]; rfl
      have length : input.length=width+registers+payload.length+2 := by rw [shape,MachineInput.envelope_length]
      have trace := setup_execution width registers payload
      rw [← shape] at trace
      exact ⟨_,_,by simpa only [setupResult, first, second] using trace,by omega,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (setup.code label))) ≤ 315 := by
  simpa [setup, bootstrap, moveMachine, restoreMachine, headers, readSave,
    headerMachine, GuardedLink.program, link, StackFrames.relocate, reverseProgram] using finiteTM_resident setup

theorem saved_width (frame : Port → List Bool) (width registers : Nat) (counter source word : List Bool) :
    bank (savedFrame frame width registers) counter source word (some 8) = List.replicate width true := by
  rw [bank_other _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
  simp [savedFrame]

theorem saved_registers (frame : Port → List Bool) (width registers : Nat) (counter source word : List Bool) :
    bank (savedFrame frame width registers) counter source word (some 9) = List.replicate registers true := by
  rw [bank_other _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
  simp [savedFrame]

end Controller.Complexity.ColdInput
