module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.ImageAssembly

@[expose] public section

/-! A single fixed binary-stack program accepts a self-describing RAM image
from input-only storage. Cold headers, capacity checking, program parsing and
state parsing are executed. A mathematical readout relates actual saved banks
to the literal image decoder; output emission is a separate machine operation. -/
namespace Controller.Complexity.ImageReader
open StackMachine WordReader
open CheckedWordField (mass)
open scoped BigOperators

def program := GuardedLink.program ImageHeaders.program ImageAssembly.program none Option.isNone

def storedBytes (input : Port → List Bool) : List Bool :=
  input (some 8)++false :: (input (some 9)++false :: ImageAssembly.bodyBytes input)

def observe (input : Port → List Bool) := MachineInput.decode (storedBytes input)

def polynomial (size : Nat) := 32*size^4+256*size^3+484*size^2+643*size+261

def pack (width registers : Nat) (bound : registers ≤ 2^width)
    (value : List (Controller.Cost.Instruction width registers) × Controller.Cost.State width registers) : MachineInput.Image :=
  ⟨width,registers,bound,value.1.toArray,value.2⟩

theorem decode_envelope (width registers : Nat) (bound : registers ≤ 2^width) (source : List Bool) :
    MachineInput.decode (MachineInput.envelope width registers source)=
      (ImageAssembly.read width registers source).map (pack width registers bound) := by
  simp only [MachineInput.decode,MachineInput.envelope,Encoding.readCount_frame,Bind.bind,Option.bind,dite_eq_left bound]
  cases countRead : Encoding.readCount source with
  | none => simp [countRead,ImageAssembly.read,ProgramSyntax.readPrefix]
  | some pair =>
    rcases pair with ⟨count,payload⟩
    cases programRead : InstructionCodec.readMany width registers count payload with
    | none => simp [countRead,programRead,ImageAssembly.read,ProgramSyntax.readPrefix]
    | some pair =>
      rcases pair with ⟨instructions,suffix⟩
      cases stateRead : MachineBridge.decodeState width registers suffix <;>
        simp [countRead,programRead,stateRead,ImageAssembly.read,ProgramSyntax.readPrefix,pack]

theorem reject_headers (input : List Bool) (rejected : ImageHeaders.readHeaders input=none) : MachineInput.decode input=none := by
  cases first : Encoding.readCount input with
  | none => simp [MachineInput.decode,first]
  | some pair =>
    rcases pair with ⟨width,rest⟩
    cases second : Encoding.readCount rest with
    | none => simp [MachineInput.decode,first,second]
    | some pair =>
      rcases pair with ⟨registers,payload⟩
      by_cases bound : registers ≤ 2^width
      · simp [ImageHeaders.readHeaders,first,second,bound] at rejected
      · simp [MachineInput.decode,first,second,bound]

theorem body_monotone (small large : Nat) (bounded : small ≤ large) : ImageAssembly.polynomial small ≤ ImageAssembly.polynomial large := by
  have fourth := Nat.pow_le_pow_left bounded 4
  have cube := Nat.pow_le_pow_left bounded 3
  have square := Nat.pow_le_pow_left bounded 2
  unfold ImageAssembly.polynomial
  omega

theorem reject_time (size ticks : Nat) (bounded : ticks ≤ 4*size^2+28*size+34) : ticks+1 ≤ polynomial size := by
  unfold polynomial
  omega

theorem join_time (size stored first second : Nat) (smaller : stored ≤ size)
    (firstBound : first ≤ 4*size^2+28*size+34) (secondBound : second ≤ ImageAssembly.polynomial stored) :
    first+second ≤ polynomial size := by
  have next := body_monotone stored size smaller
  unfold polynomial ImageAssembly.polynomial at *
  omega

theorem total_decodes (input : List Bool) :
    ∃ ticks peak output, Execution program (initial program input) ⟨none,output⟩ ticks peak ∧
      ticks ≤ polynomial input.length ∧ peak ≤ polynomial input.length+input.length ∧
      Option.isNone ((output none).head?)=(MachineInput.decode input).isSome ∧
      (∀ image, MachineInput.decode input=some image →
        storedBytes output=input ∧ observe output=some image ∧ output none=[] ∧ output (some 0)=[]) := by
  cases headerRead : ImageHeaders.readHeaders input with
  | none =>
    obtain ⟨ticks,peak,first,timeBound,spaceBound,accepted⟩ := ImageHeaders.total_execution input
    rw [ColdInput.initial_bank] at first
    have rejected : Option.isNone ((ImageHeaders.result input none).head?)=false := by simpa only [headerRead,Option.isSome_none] using accepted
    have trace := GuardedLink.failure ImageAssembly.program none Option.isNone first rejected
    change Execution program ⟨some program.main,_⟩ _ _ _ at trace
    rw [← ColdInput.initial_bank program] at trace
    have finalTime := reject_time input.length ticks timeBound
    have space := trace.peak_le
    rw [live_initial] at space
    have decoded := reject_headers input headerRead
    refine ⟨ticks+1,peak,ImageHeaders.result input,trace,finalTime,by omega,?_,?_⟩
    · simpa only [decoded,Option.isSome_none] using rejected
    · intro image impossible
      simp [decoded] at impossible
  | some tuple =>
    rcases tuple with ⟨width,registers,payload⟩
    obtain ⟨shape,bound⟩ := ImageHeaders.read_sound headerRead
    obtain ⟨headerTicks,headerPeak,first,headerTime,headerSpace⟩ := ImageHeaders.success_execution headerRead
    rw [ColdInput.initial_bank] at first
    obtain ⟨bodyTicks,bodyPeak,output,second,bodyTime,bodySpace,bodyAccepted,bodyObserved⟩ :=
      ImageAssembly.total_execution width registers bound payload
    have trace := GuardedLink.success none Option.isNone first second (by simp [ImageHeaders.data_at])
    change Execution program ⟨some program.main,_⟩ _ _ _ at trace
    rw [← ColdInput.initial_bank program] at trace
    have storedBound : mass (ImageHeaders.data width registers [] payload) ≤ input.length := by
      rw [ImageAssembly.header_mass,shape,MachineInput.envelope_length]
      omega
    have finalTime := join_time input.length (mass (ImageHeaders.data width registers [] payload)) headerTicks bodyTicks storedBound headerTime bodyTime
    have space := trace.peak_le
    rw [live_initial] at space
    have decoder : MachineInput.decode input=(ImageAssembly.read width registers payload).map (pack width registers bound) := by
      rw [shape,decode_envelope width registers bound payload]
    refine ⟨headerTicks+bodyTicks,max headerPeak bodyPeak,output,trace,finalTime,by omega,?_,?_⟩
    · rw [decoder,Option.isSome_map]
      exact bodyAccepted
    · intro image decoded
      cases bodyRead : ImageAssembly.read width registers payload with
      | none => simp [decoder,bodyRead] at decoded
      | some pair =>
        rcases pair with ⟨instructions,state⟩
        obtain ⟨bodyBytes,savedWidth,savedRegisters,clean,eof⟩ := bodyObserved instructions state bodyRead
        have bytes : storedBytes output=input := by
          rw [storedBytes,savedWidth,savedRegisters,bodyBytes,shape]
          rfl
        exact ⟨bytes,by rw [observe,bytes,decoded],clean,eof⟩

theorem encoded_total (image : MachineInput.Image) :
    ∃ ticks peak output, Execution program (initial program (MachineInput.encode image)) ⟨none,output⟩ ticks peak ∧
      ticks ≤ polynomial (MachineInput.encode image).length ∧ peak ≤ polynomial (MachineInput.encode image).length+(MachineInput.encode image).length ∧
      output none=[] ∧ storedBytes output=MachineInput.encode image ∧ observe output=some image := by
  obtain ⟨ticks,peak,output,trace,timeBound,spaceBound,accepted,observed⟩ := total_decodes (MachineInput.encode image)
  obtain ⟨bytes,observation,clean,eof⟩ := observed image (MachineInput.decode_encode image)
  exact ⟨ticks,peak,output,trace,timeBound,spaceBound,clean,bytes,observation⟩

theorem header_card : Fintype.card (StateReader.LabelsOf ImageHeaders.program)=77 := by
  simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,WordBound.Label,WordBound.BodyLabel,Nat.reduceAdd]

theorem canonical_card : Fintype.card (StateReader.LabelsOf program)=1403 := by
  have same : Fintype.card (StateReader.LabelsOf program)=
      Fintype.card (StateReader.LabelsOf ImageHeaders.program ⊕ Option (StateReader.LabelsOf ImageAssembly.program)) :=
    @Fintype.card_congr _ (StateReader.LabelsOf ImageHeaders.program ⊕ Option (StateReader.LabelsOf ImageAssembly.program)) _ _ (Equiv.refl _)
  have decomposed : Fintype.card (StateReader.LabelsOf ImageHeaders.program ⊕ Option (StateReader.LabelsOf ImageAssembly.program))=
      Fintype.card (StateReader.LabelsOf ImageHeaders.program)+(Fintype.card (StateReader.LabelsOf ImageAssembly.program)+1) := by
    simp only [Fintype.card_sum,Fintype.card_option]
  rw [header_card,ImageAssembly.canonical_card] at decomposed
  exact same.trans decomposed

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 12627 := by
  have bound := finiteTM_resident (K := Fin 31) (Q := StateReader.LabelsOf program) program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.ImageReader
