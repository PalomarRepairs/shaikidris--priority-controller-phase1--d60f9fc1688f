module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.InstructionFetch
public import Controller.Complexity.PcRead

public import Mathlib.Tactic.Ring

@[expose] public section

/-! The actual singleton PC field drives native instruction fetch. Both PC
extraction and program traversal are charged fixed finite routines; successful
physical operand/tag fields observe exactly the native program's indexed entry. -/
namespace Controller.Complexity.PcFetch
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (pc : Controller.Cost.Word width)
    extends PcRead.Ready input pc where
  codeStored : input (some 19)=InstructionCodec.encodeMany bound instructions
  countStored : input (some 15)=List.replicate instructions.length true
  saved : input (some 9)=List.replicate registers true

theorem Ready.fetch (input : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (pc : Controller.Cost.Word width) (ready : Ready input bound instructions pc) :
    InstructionFetch.Ready (PcRead.output input pc) bound instructions (Encoding.bits width pc.val) where
  codeStored := by simpa [PcRead.output] using ready.codeStored
  countStored := by simpa [PcRead.output] using ready.countStored
  indexStored := by simp [PcRead.output]
  clear := by
    intro port member
    have outside : port ≠ (some 3 : Port) := by intro equal; subst port; simp [FetchSetup.work] at member
    simpa only [PcRead.output,Function.update_of_ne outside] using ready.clear port member
  stored := by simpa [PcRead.output] using ready.stored
  saved := by simpa [PcRead.output] using ready.saved

def PcLabel : Type := StateReader.LabelsOf PcRead.program
instance pcFintype : Fintype PcLabel := inferInstanceAs (Fintype (StateReader.LabelsOf PcRead.program))
def pcProgram : Program (Fin 31) PcLabel := PcRead.program

def Label : Type := PcLabel ⊕ InstructionFetch.Label
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (PcLabel ⊕ InstructionFetch.Label))
def program : Program (Fin 31) Label := link pcProgram InstructionFetch.program

def result (input : Port → List Bool) (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers)) (pc : Controller.Cost.Word width) :=
  InstructionFetch.result (PcRead.output input pc) bound instructions (Encoding.bits width pc.val)

theorem execution (input : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (pc : Controller.Cost.Word width) (ready : Ready input bound instructions pc) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,result input bound instructions pc⟩ ticks peak ∧
      ticks ≤ 12*(FetchSetup.size input)^3+197*(FetchSetup.size input)^2+434*FetchSetup.size input+104 ∧
      peak ≤ 12*(FetchSetup.size input)^3+197*(FetchSetup.size input)^2+435*FetchSetup.size input+104 := by
  obtain ⟨pcTicks,pcPeak,pcRun,pcBound,_⟩ := PcRead.execution input pc ready.toReady
  obtain ⟨fetchTicks,fetchPeak,fetchRun,fetchBound⟩ := InstructionFetch.execution (PcRead.output input pc) bound instructions
    (Encoding.bits width pc.val) (ready.fetch input bound instructions pc)
  simp only [Encoding.bits_length] at fetchBound
  have cell (port : Port) : (input port).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have codeBound : (InstructionCodec.encodeMany bound instructions).length ≤ FetchSetup.size input := by simpa only [ready.codeStored] using cell (some 19)
  have nBound : instructions.length ≤ FetchSetup.size input := by simpa only [ready.countStored,List.length_replicate] using cell (some 15)
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored,List.length_replicate] using cell (some 8)
  have rBound : registers ≤ FetchSetup.size input := by simpa only [ready.saved,List.length_replicate] using cell (some 9)
  have pairs := Nat.mul_le_mul wBound rBound
  have product : 12*width*registers ≤ 12*(FetchSetup.size input)^2 := by
    calc
      _ = 12*(width*registers) := by ring
      _ ≤ 12*(FetchSetup.size input*FetchSetup.size input) := Nat.mul_le_mul_left 12 pairs
      _ = _ := by ring
  have oneBound : InstructionFetch.perInstruction width registers ≤ 12*(FetchSetup.size input)^2+159*FetchSetup.size input+301 := by
    dsimp only [InstructionFetch.perInstruction]; omega
  have repeated := Nat.mul_le_mul nBound oneBound
  have indices := Nat.mul_le_mul wBound (Nat.add_le_add_right (Nat.mul_le_mul_left 11 nBound) 33)
  have identity : 6*FetchSetup.size input+FetchSetup.size input*(11*FetchSetup.size input+33)+12*FetchSetup.size input+
      FetchSetup.size input*(12*(FetchSetup.size input)^2+159*FetchSetup.size input+301)+44=
      12*(FetchSetup.size input)^3+170*(FetchSetup.size input)^2+352*FetchSetup.size input+44 := by ring
  have fetchedBound : fetchTicks ≤ 12*(FetchSetup.size input)^3+170*(FetchSetup.size input)^2+352*FetchSetup.size input+44 := by rw [← identity]; omega
  have totalBound : pcTicks+fetchTicks ≤ 12*(FetchSetup.size input)^3+197*(FetchSetup.size input)^2+434*FetchSetup.size input+104 := by omega
  have trace := pcRun.link fetchRun
  have space := trace.peak_le
  change max pcPeak fetchPeak ≤ FetchSetup.size input+(pcTicks+fetchTicks) at space
  refine ⟨pcTicks+fetchTicks,max pcPeak fetchPeak,?_,totalBound,by omega⟩
  simpa only [program,pcProgram,Label,PcLabel,result] using trace

theorem observation (input : Port → List Bool) (bound : registers ≤ 2^width)
    (instructions : List (Controller.Cost.Instruction width registers)) (pc : Controller.Cost.Word width) :
    Option.isNone ((result input bound instructions pc none).head?)=(instructions[pc.val]?).isSome ∧
    (∀ instruction, instructions[pc.val]?=some instruction → InstructionFields.observe width registers (result input bound instructions pc)=some instruction) := by
  simpa only [result,Encoding.value_bits width pc.val pc.isLt] using InstructionFetch.observation (PcRead.output input pc) bound instructions (Encoding.bits width pc.val)

theorem pc_card : Fintype.card PcLabel=180 := by
  have original : Fintype.card (StateReader.LabelsOf PcRead.program)=180 := by
    simp only [StateReader.LabelsOf,Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd]
  have same : Fintype.card PcLabel=Fintype.card (StateReader.LabelsOf PcRead.program) :=
    @Fintype.card_congr PcLabel (StateReader.LabelsOf PcRead.program) _ _ (Equiv.refl _)
  exact same.trans original

theorem canonical_card : Fintype.card Label=1895 := by
  have split : Fintype.card Label=Fintype.card PcLabel+Fintype.card InstructionFetch.Label := Fintype.card_sum
  rw [pc_card,InstructionFetch.canonical_card] at split
  exact split

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 17055 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.PcFetch
