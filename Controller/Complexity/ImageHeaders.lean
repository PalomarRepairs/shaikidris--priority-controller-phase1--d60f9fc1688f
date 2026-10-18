module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.RegisterCapacity
public import Controller.Complexity.ColdInput

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Cold image-header validation executes both unary reads and the global
register-capacity check. Every binary input halts; successful endpoints retain
both counts and the exact remaining source. -/
namespace Controller.Complexity.ImageHeaders
open StackMachine WordReader
open scoped BigOperators

def data (width registers : Nat) (status payload : List Bool) : Port → List Bool :=
  bank (ColdInput.savedFrame ColdInput.emptyFrame width registers) status payload []

theorem data_at (width registers : Nat) (status payload : List Bool) (address : Port) :
    data width registers status payload address=
      if address=none then status else if address=some 0 then payload else if address=some 8 then List.replicate width true
      else if address=some 9 then List.replicate registers true else [] := by
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases ht : address=some 2 <;> by_cases h₈ : address=some 8 <;> by_cases h₉ : address=some 9 <;>
    simp_all [data, bank, cursorFrame, cursorPorts_apply, StackFrames.embedStorage, StackBlocks.layout,
      ColdInput.savedFrame, ColdInput.emptyFrame]

theorem capacity_bank (width registers : Nat) (status payload : List Bool) :
    RegisterRange.bank (data width registers [] payload) status [] [] []=data width registers status payload := by
  funext address
  by_cases hc : address=none <;> by_cases hw : address=some 1 <;> by_cases hb : address=some 16 <;>
    by_cases ht : address=some 17 <;> simp_all [RegisterRange.bank_at, data_at]

theorem capacity_execution (width registers : Nat) (payload : List Bool) :
    ∃ ticks peak, Execution RegisterCapacity.program
      ⟨some RegisterCapacity.program.main,data width registers [] payload⟩
      ⟨none,data width registers (if registers ≤ 2^width then [] else [false]) payload⟩ ticks peak ∧
      ticks ≤ width*(4*registers+10)+6*registers+18 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := RegisterCapacity.execution (data width registers [] payload) width registers
    (by simp [data_at]) (by simp [data_at])
  simp only [RegisterCapacity.bank,capacity_bank] at trace
  exact ⟨ticks,peak,trace,timeBound⟩

def program := GuardedLink.program ColdInput.setup RegisterCapacity.program none Option.isNone

theorem execution (width registers : Nat) (payload : List Bool) :
    ∃ ticks peak, Execution program (initial program (MachineInput.envelope width registers payload))
      ⟨none,data width registers (if registers ≤ 2^width then [] else [false]) payload⟩ ticks peak ∧
      ticks ≤ 4*(MachineInput.envelope width registers payload).length^2+
        28*(MachineInput.envelope width registers payload).length+34 ∧
      peak ≤ 4*(MachineInput.envelope width registers payload).length^2+
        29*(MachineInput.envelope width registers payload).length+34 := by
  have first := ColdInput.setup_execution width registers payload
  rw [ColdInput.initial_bank] at first
  obtain ⟨capTicks,capPeak,second,capTime⟩ := capacity_execution width registers payload
  have trace := GuardedLink.success none Option.isNone first second (by simp [bank_counter])
  change Execution program ⟨some program.main,_⟩ _ _ _ at trace
  rw [← ColdInput.initial_bank program] at trace
  let n := (MachineInput.envelope width registers payload).length
  have length : n=width+registers+payload.length+2 := MachineInput.envelope_length _ _ _
  have wBound : width ≤ n := by omega
  have rBound : registers ≤ n := by omega
  have product := Nat.mul_le_mul wBound (Nat.add_le_add_right (Nat.mul_le_mul_left 4 rBound) 10)
  have identity : n*(4*n+10)+6*n+18+12*n+16=4*n^2+28*n+34 := by ring
  have timeBound : 8*n+4*width+4*registers+16+capTicks ≤ 4*n^2+28*n+34 := by omega
  have space := trace.peak_le
  rw [live_initial] at space
  have peakIdentity : n+(4*n^2+28*n+34)=4*n^2+29*n+34 := by ring
  exact ⟨_,_,trace,timeBound,space.trans ((Nat.add_le_add_left timeBound _).trans_eq peakIdentity)⟩

def readHeaders (input : List Bool) : Option (Nat × Nat × List Bool) := do
  let (width,rest) ← Encoding.readCount input
  let (registers,payload) ← Encoding.readCount rest
  if registers ≤ 2^width then some (width,registers,payload) else none

def result (input : List Bool) : Port → List Bool :=
  match Encoding.readCount input with
  | none => ColdInput.setupResult input
  | some (width,rest) => match Encoding.readCount rest with
    | none => ColdInput.setupResult input
    | some (registers,payload) => data width registers (if registers ≤ 2^width then [] else [false]) payload

theorem total_execution (input : List Bool) :
    ∃ ticks peak, Execution program (initial program input) ⟨none,result input⟩ ticks peak ∧
      ticks ≤ 4*input.length^2+28*input.length+34 ∧ peak ≤ 4*input.length^2+29*input.length+34 ∧
      Option.isNone ((result input none).head?)=(readHeaders input).isSome := by
  cases firstRead : Encoding.readCount input with
  | none =>
    obtain ⟨ticks,peak,first,timeBound,spaceBound⟩ := ColdInput.total_setup input
    rw [ColdInput.initial_bank] at first
    have rejected : Option.isNone ((ColdInput.setupResult input none).head?)=false := by
      simp [ColdInput.setupResult,firstRead,bank_counter]
    have trace := GuardedLink.failure RegisterCapacity.program none Option.isNone first rejected
    change Execution program ⟨some program.main,_⟩ _ _ _ at trace
    rw [← ColdInput.initial_bank program] at trace
    refine ⟨ticks+1,peak,?_,by omega,by omega,?_⟩
    · simpa only [result,firstRead] using trace
    · simp [result,readHeaders,firstRead,ColdInput.setupResult,bank_counter]
  | some pair =>
    rcases pair with ⟨width,rest⟩
    cases secondRead : Encoding.readCount rest with
    | none =>
      obtain ⟨ticks,peak,first,timeBound,spaceBound⟩ := ColdInput.total_setup input
      rw [ColdInput.initial_bank] at first
      have rejected : Option.isNone ((ColdInput.setupResult input none).head?)=false := by
        simp [ColdInput.setupResult,firstRead,secondRead,bank_counter]
      have trace := GuardedLink.failure RegisterCapacity.program none Option.isNone first rejected
      change Execution program ⟨some program.main,_⟩ _ _ _ at trace
      rw [← ColdInput.initial_bank program] at trace
      refine ⟨ticks+1,peak,?_,by omega,by omega,?_⟩
      · simpa only [result,firstRead,secondRead] using trace
      · simp [result,readHeaders,firstRead,secondRead,ColdInput.setupResult,bank_counter]
    | some pair =>
      rcases pair with ⟨registers,payload⟩
      have shape : input=MachineInput.envelope width registers payload := by
        rw [HeaderParser.readCount_sound firstRead,HeaderParser.readCount_sound secondRead]
        rfl
      obtain ⟨ticks,peak,trace,timeBound,spaceBound⟩ := execution width registers payload
      rw [← shape] at trace timeBound spaceBound
      refine ⟨ticks,peak,?_,timeBound,spaceBound,?_⟩
      · simpa only [result,firstRead,secondRead] using trace
      · by_cases valid : registers ≤ 2^width <;> simp [result,readHeaders,firstRead,secondRead,valid,data_at]

theorem read_sound {input : List Bool} {width registers : Nat} {payload : List Bool}
    (parsed : readHeaders input=some (width,registers,payload)) :
    input=MachineInput.envelope width registers payload ∧ registers ≤ 2^width := by
  unfold readHeaders at parsed
  cases first : Encoding.readCount input with
  | none => simp [first] at parsed
  | some pair =>
    rcases pair with ⟨w,rest⟩
    cases second : Encoding.readCount rest with
    | none => simp [first,second] at parsed
    | some pair =>
      rcases pair with ⟨r,suffix⟩
      by_cases valid : r ≤ 2^w
      · simp [first,second,valid] at parsed
        rcases parsed with ⟨rfl,rfl,rfl⟩
        exact ⟨by rw [HeaderParser.readCount_sound first,HeaderParser.readCount_sound second]; rfl,valid⟩
      · simp [first,second,valid] at parsed

theorem success_execution {input : List Bool} {width registers : Nat} {payload : List Bool}
    (parsed : readHeaders input=some (width,registers,payload)) :
    ∃ ticks peak, Execution program (initial program input) ⟨none,data width registers [] payload⟩ ticks peak ∧
      ticks ≤ 4*input.length^2+28*input.length+34 ∧ peak ≤ 4*input.length^2+29*input.length+34 := by
  obtain ⟨shape,valid⟩ := read_sound parsed
  rw [shape]
  simpa only [ite_eq_left valid] using execution width registers payload

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 693 := by
  simpa [program,ColdInput.setup,ColdInput.bootstrap,ColdInput.moveMachine,ColdInput.restoreMachine,
    ColdInput.headers,ColdInput.readSave,ColdInput.headerMachine,RegisterCapacity.program,RegisterCapacity.setup,
    RegisterCapacity.widthMachine,RegisterRange.copyMachine,RegisterRange.coreMachine,GuardedLink.program,
    link,StackFrames.relocate,StackBlocks.reverseProgram] using finiteTM_resident program

end Controller.Complexity.ImageHeaders
