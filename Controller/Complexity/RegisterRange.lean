module

public import Mathlib.Tactic.Ring

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordBound
public import Controller.Complexity.StackCopy
public import Controller.Complexity.MachineBridge
public import Controller.Complexity.WordReader

@[expose] public section

/-! An existing binary operand is checked against the saved unary register
count. Copying the count and publishing the status are actual instructions.
The operand is consumed; both working-bound banks are cleared. All other
banks, including the source stream and original operand payload, are preserved. -/
namespace Controller.Complexity.RegisterRange
open StackMachine StackBlocks WordReader
open scoped BigOperators

def bank (frame : Port → List Bool) (status word bound scratch : List Bool) : Port → List Bool :=
  Function.update (Function.update (Function.update (Function.update frame none status)
    (some 1) word) (some 16) bound) (some 17) scratch

theorem bank_at (frame : Port → List Bool) (status word bound scratch : List Bool) (target : Port) :
    bank frame status word bound scratch target = if target=none then status else if target=some 1 then word
      else if target=some 16 then bound else if target=some 17 then scratch else frame target := by
  by_cases hs : target=none <;> by_cases hw : target=some 1 <;>
    by_cases hb : target=some 16 <;> by_cases ht : target=some 17 <;> simp_all [bank]

def copyPorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 9) (some 16) (some 17) (by decide) (by decide) (by decide)

def corePorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 1) (some 16) (some 17) (by decide) (by decide) (by decide)

theorem copyPorts_apply (port : Option Bool) : copyPorts port =
    (match port with | none => some 9 | some false => some 16 | some true => some 17) := rfl

theorem corePorts_apply (port : Option Bool) : corePorts port =
    (match port with | none => some 1 | some false => some 16 | some true => some 17) := rfl

theorem copy_storage (frame : Port → List Bool) (word bound scratch : List Bool) (registers : Nat)
    (saved : frame (some 9)=List.replicate registers true) :
    StackFrames.embedStorage copyPorts (bank frame [] word [] []) (layout (List.replicate registers true) bound scratch)=
      bank frame [] word bound scratch := by
  funext target
  by_cases hs : target=none <;> by_cases hw : target=some 1 <;> by_cases hr : target=some 9 <;>
    by_cases hb : target=some 16 <;> by_cases ht : target=some 17 <;>
    simp_all [StackFrames.embedStorage, copyPorts_apply, layout, bank_at]

theorem core_storage (frame : Port → List Bool) (word bound scratch : List Bool) :
    StackFrames.embedStorage corePorts (bank frame [] [] [] []) (layout word bound scratch)=bank frame [] word bound scratch := by
  funext target
  by_cases hs : target=none <;> by_cases hw : target=some 1 <;>
    by_cases hb : target=some 16 <;> by_cases ht : target=some 17 <;>
    simp_all [StackFrames.embedStorage, corePorts_apply, layout, bank_at]

theorem publish_storage (frame : Port → List Bool) (status word : List Bool) :
    storage (bank frame [] [] [] []) (some 1) none word status=bank frame status word [] [] := by
  funext target
  by_cases hs : target=none <;> by_cases hw : target=some 1 <;>
    by_cases hb : target=some 16 <;> by_cases ht : target=some 17 <;> simp_all [storage, bank_at]

def copyMachine := StackFrames.relocate copyPorts StackCopy.program
def coreMachine := StackFrames.relocate corePorts WordBound.program
def publishMachine := transfer (K := Fin 31) (some 1) none
abbrev Label := ((Fin 4 ⊕ Fin 6) ⊕ WordBound.Label) ⊕ Fin 4
def program : Program (Fin 31) Label := link (link copyMachine coreMachine) publishMachine

theorem copy_execution (frame : Port → List Bool) (word : List Bool) (registers : Nat)
    (saved : frame (some 9)=List.replicate registers true) :
    ∃ peak, Execution copyMachine ⟨some copyMachine.main,bank frame [] word [] []⟩
      ⟨none,bank frame [] word (List.replicate registers true) []⟩ (5*registers+4) peak := by
  have trace := StackCopy.framed_execution copyPorts (bank frame [] word [] []) (List.replicate registers true) []
  exact ⟨_,by simpa only [copyMachine, StackFrames.relocate, StackFrames.embedState, List.length_replicate,
    List.append_nil, copy_storage frame word _ _ registers saved] using trace⟩

theorem core_execution (frame : Port → List Bool) (word : List Bool) (registers : Nat) :
    ∃ ticks peak, Execution coreMachine ⟨some coreMachine.main,bank frame [] word (List.replicate registers true) []⟩
      ⟨none,bank frame [] (if Encoding.value word < registers then [] else [false]) [] []⟩ ticks peak ∧
      ticks ≤ word.length*(4*registers+5)+registers+5 := by
  obtain ⟨ticks,peak,trace,bound⟩ := WordBound.execution word registers
  have lifted := StackFrames.execution corePorts (bank frame [] [] [] []) trace
  exact ⟨ticks,_,by simpa only [coreMachine, StackFrames.relocate, StackFrames.embedState,
    WordBound.state, core_storage] using lifted,bound⟩

theorem publish_execution (frame : Port → List Bool) (accepted : Prop) [Decidable accepted] :
    ∃ ticks peak, Execution publishMachine
      ⟨some publishMachine.main,bank frame [] (if accepted then [] else [false]) [] []⟩
      ⟨none,bank frame (if accepted then [] else [false]) [] [] []⟩ ticks peak ∧ ticks ≤ 4 := by
  by_cases success : accepted
  · have trace := transfer_execution (bank frame [] [] [] []) (source := some 1) (destination := none) (by decide) [] []
    refine ⟨2,live (state (some 0) (bank frame [] [] [] []) (some 1) none [] []),?_,by decide⟩
    simpa only [publishMachine, transfer, state, publish_storage, ite_eq_left success, List.reverse_nil, List.nil_append,
      List.length_nil, Nat.mul_zero, Nat.zero_add] using trace
  · have trace := transfer_execution (bank frame [] [] [] []) (source := some 1) (destination := none) (by decide) [false] []
    refine ⟨4,live (state (some 0) (bank frame [] [] [] []) (some 1) none [false] []),?_,le_rfl⟩
    simpa only [publishMachine, transfer, state, publish_storage, ite_eq_right success, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append, List.length_cons, List.length_nil] using trace

theorem execution (frame : Port → List Bool) (word : List Bool) (registers : Nat)
    (saved : frame (some 9)=List.replicate registers true) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] word [] []⟩
      ⟨none,bank frame (if Encoding.value word < registers then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ word.length*(4*registers+5)+6*registers+13 := by
  obtain ⟨copyPeak,copying⟩ := copy_execution frame word registers saved
  obtain ⟨coreTicks,corePeak,testing,coreBound⟩ := core_execution frame word registers
  obtain ⟨publishTicks,publishPeak,publishing,publishBound⟩ := publish_execution frame (Encoding.value word < registers)
  have trace := (copying.link testing).link publishing
  exact ⟨_,_,trace,by omega⟩

theorem encoded_status (frame : Port → List Bool) (index : Controller.Cost.Word width) (registers : Nat)
    (saved : frame (some 9)=List.replicate registers true) :
    ∃ final ticks peak, Execution program ⟨some program.main,bank frame [] (Encoding.bits width index.val) [] []⟩ final ticks peak ∧
      Option.isNone (final.stk none).head?=(InstructionCodec.readRegister (registers := registers) index).isSome ∧
      ticks ≤ width*(4*registers+5)+6*registers+13 := by
  obtain ⟨ticks,peak,trace,bound⟩ := execution frame (Encoding.bits width index.val) registers saved
  have decoded : Encoding.value (Encoding.bits width index.val)=index.val :=
    Encoding.value_bits width index.val index.isLt
  rw [decoded] at trace
  refine ⟨_,ticks,peak,trace,?_,?_⟩
  · by_cases valid : index.val < registers <;> simp [bank_at, InstructionCodec.readRegister, valid]
  · simpa only [Encoding.bits_length] using bound

theorem ready_bank (input : Port → List Bool) (statusClean : input none=[])
    (boundClean : input (some 16)=[]) (scratchClean : input (some 17)=[]) :
    bank input [] (input (some 1)) [] []=input := by
  funext target
  by_cases hs : target=none <;> by_cases hw : target=some 1 <;>
    by_cases hb : target=some 16 <;> by_cases ht : target=some 17 <;> simp_all [bank_at]

theorem ready_execution (input : Port → List Bool) (registers : Nat)
    (statusClean : input none=[]) (boundClean : input (some 16)=[])
    (scratchClean : input (some 17)=[]) (saved : input (some 9)=List.replicate registers true) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩
      ⟨none,bank input (if Encoding.value (input (some 1)) < registers then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ (input (some 1)).length*(4*registers+5)+6*registers+13 := by
  simpa only [ready_bank input statusClean boundClean scratchClean] using
    execution input (input (some 1)) registers saved

theorem cell_bound (frame : Port → List Bool) (word : List Bool) (port : Port) :
    (bank frame [] word [] [] port).length ≤ live (⟨some program.main,bank frame [] word [] []⟩ : State (Fin 31) Label) :=
  Finset.single_le_sum (f := fun target : Port => (bank frame [] word [] [] target).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)

theorem total_polynomial (frame : Port → List Bool) (word : List Bool) (registers : Nat)
    (saved : frame (some 9)=List.replicate registers true) :
    ∃ ticks peak, Execution program ⟨some program.main,bank frame [] word [] []⟩
      ⟨none,bank frame (if Encoding.value word < registers then [] else [false]) [] [] []⟩ ticks peak ∧
      ticks ≤ 4*(live (⟨some program.main,bank frame [] word [] []⟩ : State (Fin 31) _))^2+
        11*live (⟨some program.main,bank frame [] word [] []⟩ : State (Fin 31) _)+13 ∧
      peak ≤ 4*(live (⟨some program.main,bank frame [] word [] []⟩ : State (Fin 31) _))^2+
        12*live (⟨some program.main,bank frame [] word [] []⟩ : State (Fin 31) _)+13 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution frame word registers saved
  let initialSize := live (⟨some program.main,bank frame [] word [] []⟩ : State (Fin 31) _)
  have wordBound : word.length ≤ initialSize := by simpa [initialSize, bank_at] using cell_bound frame word (some 1)
  have registerBound : registers ≤ initialSize := by simpa [initialSize, bank_at, saved] using cell_bound frame word (some 9)
  have product := Nat.mul_le_mul wordBound (Nat.add_le_add_right (Nat.mul_le_mul_left 4 registerBound) 5)
  have identity : initialSize*(4*initialSize+5)+6*initialSize+13=4*initialSize^2+11*initialSize+13 := by ring
  have finalTime : ticks ≤ 4*initialSize^2+11*initialSize+13 := by rw [← identity]; omega
  have space := trace.peak_le
  exact ⟨ticks,peak,trace,finalTime,by dsimp [initialSize] at *; omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 270 := by
  simpa [program, copyMachine, coreMachine, publishMachine, StackFrames.relocate,
    StackCopy.program, WordBound.program, WordBound.cycle, UnaryHalf.program, link] using finiteTM_resident program

end Controller.Complexity.RegisterRange
