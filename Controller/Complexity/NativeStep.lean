module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeDispatch

@[expose] public section

/-! The persistent native PC drives program fetch and the fetched four-bit
tag drives execution. Invalid PCs reject before entering any native body. -/
namespace Controller.Complexity.NativeStep
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers)) : Prop where
  stored : NativeStore.Stored input state
  running : state.halted=false
  codeStored : input (some 19)=InstructionCodec.encodeMany bound instructions
  countStored : input (some 15)=List.replicate instructions.length true
  indexEmpty : input (some 3)=[]
  valueEmpty : input (some 27)=[]
  bufferEmpty : input (some 28)=[]
  resultEmpty : input (some 29)=[]
  clear : ∀ port ∈ FetchSetup.work, input port=[]
  extraClear : input (some 20)=[]

def fetched := @PcFetch.result
def output (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers)) :=
  if valid : state.pc.val < instructions.length then
    NativeDispatch.output (fetched input bound instructions state.pc) state bound instructions[state.pc.val]
  else fetched input bound instructions state.pc

def Label : Type := PcFetch.Label ⊕ Option NativeDispatch.Label
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (PcFetch.Label ⊕ Option NativeDispatch.Label))
def program : Program (Fin 31) Label := GuardedLink.program PcFetch.program NativeDispatch.program none Option.isNone
def fetchBudget (mass : Nat) := 12*mass^3+197*mass^2+434*mass+104
def budget (mass : Nat) := fetchBudget mass+12000*(mass+fetchBudget mass)^2+10003*(mass+fetchBudget mass)+4011

theorem Ready.fetch (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (r : Ready input state bound instructions) : PcFetch.Ready input bound instructions state.pc where
  stored := r.stored.widthStored
  pcStored := by simpa [FieldGet.field] using r.stored.pcStored
  indexEmpty := r.indexEmpty
  clear := r.clear
  codeStored := r.codeStored
  countStored := r.countStored
  saved := r.stored.countStored

theorem fetched_shape (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (valid : state.pc.val < instructions.length) :
    fetched input bound instructions state.pc=InstructionFetch.chosen (PcRead.output input state.pc) bound instructions[state.pc.val] := by
  simp only [fetched,PcFetch.result,InstructionFetch.result,Encoding.value_bits width state.pc.val state.pc.isLt,dite_eq_left valid]

theorem Ready.body (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (r : Ready input state bound instructions) (valid : state.pc.val < instructions.length) :
    NativeDispatch.Ready (fetched input bound instructions state.pc) state bound instructions[state.pc.val] := by
  have shape := fetched_shape input state bound instructions valid
  have stored : NativeStore.Stored (fetched input bound instructions state.pc) state := by
    constructor
    all_goals rw [shape]
    · simpa [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output] using r.stored.widthStored
    · simpa [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output] using r.stored.countStored
    · simpa [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output] using r.stored.registersStored
    · simpa [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output] using r.stored.heapStored
    · simpa [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output] using r.stored.stackStored
    · simpa [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output] using r.stored.outputStored
    · simpa [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output] using r.stored.pcStored
    · simpa [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output] using r.stored.haltStored
  refine { stored := stored, running := r.running, payload := ?_, indexStored := ?_, valueEmpty := ?_, bufferEmpty := ?_, resultEmpty := ?_, clear := ?_, tagStored := ?_ }
  · rw [shape]
    simp [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at]
  · rw [shape]
    simp [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output]
  · rw [shape]
    simpa [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output] using r.valueEmpty
  · rw [shape]
    simpa [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output] using r.bufferEmpty
  · rw [shape]
    simpa [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output] using r.resultEmpty
  · intro port member
    rw [shape]
    simp only [FieldSet.work,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [InstructionFetch.chosen,InstructionShape.fieldsData,WordListReader.data_at,InstructionFields.resultFrame,InstructionFields.tagFrame,PcRead.output,r.extraClear]
    all_goals exact r.clear _ (by simp [FetchSetup.work])
  · rw [shape]
    exact InstructionShape.tag_stored _ _ _ _

theorem semantics (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (r : Ready input state bound instructions) :
    LoadBody.observation width registers (output input state bound instructions)=Controller.Cost.programStep instructions.toArray state := by
  by_cases valid : state.pc.val < instructions.length
  · rw [output,dite_eq_left valid,NativeDispatch.semantics _ _ _ _ (r.body input state bound instructions valid)]
    simp [Controller.Cost.programStep,valid]
  · have status := (PcFetch.observation input bound instructions state.pc).1
    change Option.isNone ((fetched input bound instructions state.pc none).head?)=(instructions[state.pc.val]?).isSome at status
    have absent : instructions[state.pc.val]?=none := List.getElem?_eq_none (Nat.le_of_not_gt valid)
    simp only [absent,Option.isSome_none] at status
    simp [output,valid,LoadBody.observation,status,Controller.Cost.programStep]

theorem execution (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (r : Ready input state bound instructions) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input state bound instructions⟩ ticks peak ∧
      ticks ≤ budget (FetchSetup.size input) ∧ peak ≤ FetchSetup.size input+budget (FetchSetup.size input) := by
  obtain ⟨fetchTicks,fetchPeak,fetch,fetchTime,_⟩ := PcFetch.execution input bound instructions state.pc (r.fetch input state bound instructions)
  change fetchTicks ≤ fetchBudget (FetchSetup.size input) at fetchTime
  have status := (PcFetch.observation input bound instructions state.pc).1
  change Option.isNone ((fetched input bound instructions state.pc none).head?)=(instructions[state.pc.val]?).isSome at status
  by_cases valid : state.pc.val < instructions.length
  · obtain ⟨bodyTicks,bodyPeak,body,bodyTime,_⟩ := NativeDispatch.execution (fetched input bound instructions state.pc) state bound instructions[state.pc.val]
      (r.body input state bound instructions valid)
    have accepted : Option.isNone ((fetched input bound instructions state.pc none).head?)=true := by
      simpa only [List.getElem?_eq_getElem valid,Option.isSome_some] using status
    have trace := GuardedLink.success none Option.isNone fetch body accepted
    have mass := fetch.final_live_le.trans fetch.peak_le
    change FetchSetup.size (fetched input bound instructions state.pc) ≤ FetchSetup.size input+fetchTicks at mass
    have enlarged := mass.trans (Nat.add_le_add_left fetchTime _)
    have squared := Nat.pow_le_pow_left enlarged 2
    have time : fetchTicks+bodyTicks ≤ budget (FetchSetup.size input) := by unfold budget; omega
    have space := trace.peak_le
    change _ ≤ FetchSetup.size input+_ at space
    refine ⟨fetchTicks+bodyTicks,max fetchPeak bodyPeak,?_,time,by omega⟩
    simpa only [program,Label,output,dite_eq_left valid] using trace
  · have rejected : Option.isNone ((fetched input bound instructions state.pc none).head?)=false := by
      simpa only [List.getElem?_eq_none (Nat.le_of_not_gt valid),Option.isSome_none] using status
    have trace := GuardedLink.failure NativeDispatch.program none Option.isNone fetch rejected
    have time : fetchTicks+1 ≤ budget (FetchSetup.size input) := by unfold budget; omega
    have space := trace.peak_le
    change _ ≤ FetchSetup.size input+_ at space
    refine ⟨fetchTicks+1,fetchPeak,?_,time,by omega⟩
    simpa only [program,Label,output,dite_eq_right valid,fetched] using trace

theorem canonical_card : Fintype.card Label=13513 := by
  change Fintype.card (PcFetch.Label ⊕ Option NativeDispatch.Label)=_
  simp only [Fintype.card_sum,Fintype.card_option,PcFetch.canonical_card,NativeDispatch.canonical_card,Nat.reduceAdd]

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 121617 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.NativeStep
