module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ShrinkFields

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Fetch setup preserves program/code/index banks, copies code and its actual
count, range-checks the binary index and constructs a bounded traversal count.
The working program count is erased before instruction parsing on both results. -/
namespace Controller.Complexity.FetchSetup
open StackMachine WordReader
open scoped BigOperators

def work : List Port := [none,some 0,some 1,some 2,some 4,some 5,some 6,some 7,some 10,some 11,some 12,some 13,some 16,some 17,some 18]

structure Ready (input : Port → List Bool) (code index : List Bool) (count : Nat) : Prop where
  codeStored : input (some 19)=code
  countStored : input (some 15)=List.replicate count true
  indexStored : input (some 3)=index
  clear : ∀ port ∈ work, input port=[]

def codePorts : Option Bool ↪ Port := StackFrames.threePorts (some 19) (some 0) (some 2) (by decide) (by decide) (by decide)
def countPorts : Option Bool ↪ Port := StackFrames.threePorts (some 15) (some 10) (some 2) (by decide) (by decide) (by decide)

theorem codePorts_apply (port : Option Bool) : codePorts port=(match port with | none => some 19 | some false => some 0 | some true => some 2) := rfl
theorem countPorts_apply (port : Option Bool) : countPorts port=(match port with | none => some 15 | some false => some 10 | some true => some 2) := rfl

def codeMachine := StackFrames.relocate codePorts StackCopy.program
def countMachine := StackFrames.relocate countPorts StackCopy.program
def checking := link IndexPlan.program (StackClear.program (some 10 : Port))
def program := link (link codeMachine countMachine) checking

def copied (input : Port → List Bool) (code : List Bool) (count : Nat) : Port → List Bool :=
  bank (Function.update input (some 10) (List.replicate count true)) [] code []

def output (input : Port → List Bool) (code index : List Bool) (count : Nat) : Port → List Bool :=
  bank (Function.update input (some 4) (if Encoding.value index<count then List.replicate (Encoding.value index) true else []))
    (if Encoding.value index<count then [] else [false]) code []

theorem code_execution (input : Port → List Bool) (code index : List Bool) (count : Nat) (ready : Ready input code index count) :
    ∃ peak, Execution codeMachine ⟨some codeMachine.main,input⟩
      ⟨none,Function.update input (some 0) code⟩ (5*code.length+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution codePorts input (by simpa only [codePorts_apply] using ready.clear (some 2) (by simp [work]))
  exact ⟨peak,by simpa only [codeMachine,StackFrames.relocate,codePorts_apply,ready.codeStored,ready.clear (some 0) (by simp [work]),List.append_nil] using trace⟩

theorem count_execution (input : Port → List Bool) (code index : List Bool) (count : Nat) (ready : Ready input code index count) :
    ∃ peak, Execution countMachine ⟨some countMachine.main,Function.update input (some 0) code⟩
      ⟨none,copied input code count⟩ (5*count+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution countPorts (Function.update input (some 0) code)
    (by simpa [countPorts_apply] using ready.clear (some 2) (by simp [work]))
  have endpoint : Function.update (Function.update input (some 0) code) (some 10) (List.replicate count true)=copied input code count := by
    funext address
    have status := ready.clear none (by simp [work])
    have word := ready.clear (some 1) (by simp [work])
    have scratch := ready.clear (some 2) (by simp [work])
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;> by_cases ht : address=some 2 <;>
      simp_all [copied,WordSkip.reader_at,Function.update_apply]
  have stored : Function.update input (some 0) code (some 15)=List.replicate count true := by simpa using ready.countStored
  have clean : Function.update input (some 0) code (some 10)=[] := by simpa using ready.clear (some 10) (by simp [work])
  simpa only [countMachine,StackFrames.relocate,countPorts_apply,stored,clean,List.append_nil,List.length_replicate,endpoint] using Exists.intro peak trace

theorem execution (input : Port → List Bool) (code index : List Bool) (count : Nat) (ready : Ready input code index count) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input code index count⟩ ticks peak ∧
      ticks ≤ 5*code.length+index.length*(11*count+33)+12*count+40 := by
  obtain ⟨codePeak,copyCode⟩ := code_execution input code index count ready
  obtain ⟨countPeak,copyCount⟩ := count_execution input code index count ready
  have clean (port : Port) (member : port ∈ work) := ready.clear port member
  obtain ⟨planTicks,planPeak,planning,planBound⟩ := IndexPlan.execution (copied input code count) index count
    (by simpa [copied,WordSkip.reader_at] using ready.indexStored) (by simp [copied,WordSkip.reader_at])
    (by simp [copied,bank_counter]) (by simp [copied,bank_word]) (by simpa [copied,WordSkip.reader_at] using clean (some 16) (by simp [work]))
    (by simpa [copied,WordSkip.reader_at] using clean (some 4) (by simp [work]))
    (by simpa [copied,WordSkip.reader_at] using clean (some 5) (by simp [work]))
    (by simpa [copied,WordSkip.reader_at] using clean (some 6) (by simp [work]))
    (by simpa [copied,WordSkip.reader_at] using clean (some 7) (by simp [work]))
    (by simpa [copied,WordSkip.reader_at] using clean (some 17) (by simp [work]))
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (IndexPlan.result (copied input code count) index count) (some 10)
  have countLength : (IndexPlan.result (copied input code count) index count (some 10)).length=count := by
    simp [IndexPlan.result,copied,WordSkip.reader_at]
  have final : Function.update (IndexPlan.result (copied input code count) index count) (some 10) []=output input code index count := by
    funext address
    have initial := ready.clear (some 10) (by simp [work])
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
      by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> by_cases hb : address=some 10 <;>
      simp_all [IndexPlan.result,copied,output,WordSkip.reader_at]
  rw [countLength,final] at clearing
  have trace := (copyCode.link copyCount).link (planning.link clearing)
  exact ⟨_,_,trace,by omega⟩

def size (input : Port → List Bool) : Nat := ∑ port : Port,(input port).length

theorem total_polynomial (input : Port → List Bool) (code index : List Bool) (count : Nat) (ready : Ready input code index count) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input code index count⟩ ticks peak ∧
      ticks ≤ 11*(size input)^2+50*size input+40 ∧ peak ≤ 11*(size input)^2+51*size input+40 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution input code index count ready
  have cell (port : Port) : (input port).length ≤ size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have codeBound : code.length ≤ size input := by simpa only [ready.codeStored] using cell (some 19)
  have indexBound : index.length ≤ size input := by simpa only [ready.indexStored] using cell (some 3)
  have nBound : count ≤ size input := by simpa only [ready.countStored,List.length_replicate] using cell (some 15)
  have product := Nat.mul_le_mul indexBound (Nat.add_le_add_right (Nat.mul_le_mul_left 11 nBound) 33)
  have identity : 5*size input+size input*(11*size input+33)+12*size input+40=11*(size input)^2+50*size input+40 := by ring
  have bounded : ticks ≤ 11*(size input)^2+50*size input+40 := by rw [← identity]; omega
  have space := trace.peak_le
  change peak ≤ size input+ticks at space
  exact ⟨ticks,peak,trace,bounded,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 963 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.FetchSetup
