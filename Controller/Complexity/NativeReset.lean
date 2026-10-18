module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeStep

@[expose] public section

/-! A fixed executed reset erases all twenty-two nonpersistent banks and
preserves native state, width/register headers, program count and code. Reset
establishes the literal workspace premises of the next native instruction. -/
namespace Controller.Complexity.NativeReset
open StackMachine WordReader
open scoped BigOperators

def Labels : List Port → Type
  | [] => Fin 1
  | _ :: rest => Fin 2 ⊕ Labels rest

instance labelsFintype (ports : List Port) : Fintype (Labels ports) := by
  induction ports with
  | nil => exact inferInstanceAs (Fintype (Fin 1))
  | cons port rest ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin 2 ⊕ Labels rest))

def chain : (ports : List Port) → Program (Fin 31) (Labels ports)
  | [] => ⟨(0 : Fin 1),fun _ => .halt⟩
  | port :: rest => link (StackClear.program port) (chain rest)

def erased (input : Port → List Bool) : List Port → Port → List Bool
  | [] => input
  | port :: rest => erased (Function.update input port []) rest

def ticks (input : Port → List Bool) : List Port → Nat
  | [] => 1
  | port :: rest => (input port).length+2+ticks (Function.update input port []) rest

theorem erased_at (input : Port → List Bool) (ports : List Port) (target : Port) :
    erased input ports target=if target ∈ ports then [] else input target := by
  induction ports generalizing input with
  | nil => rfl
  | cons port rest ih =>
    simp only [erased,ih,List.mem_cons]
    by_cases head : target=port <;> by_cases tail : target ∈ rest <;> simp [head,tail]

theorem clear_mass (input : Port → List Bool) (port : Port) :
    FetchSetup.size (Function.update input port [])+(input port).length=FetchSetup.size input := by
  have sum : (∑ target : Port, ((Function.update input port [] target).length+
      if target=port then (input port).length else 0))=FetchSetup.size input := by
    apply Finset.sum_congr rfl
    intro target _
    by_cases same : target=port <;> simp [same]
  simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,FetchSetup.size] using sum

theorem mass_balance (input : Port → List Bool) (ports : List Port) :
    ticks input ports+FetchSetup.size (erased input ports)=FetchSetup.size input+2*ports.length+1 := by
  induction ports generalizing input with
  | nil => simp [ticks,erased,Nat.add_comm]
  | cons port rest ih =>
    have next := ih (Function.update input port [])
    have removed := clear_mass input port
    simp only [ticks,erased,List.length_cons] at *
    omega

theorem chain_execution (input : Port → List Bool) (ports : List Port) :
    ∃ peak, Execution (chain ports) ⟨some (chain ports).main,input⟩ ⟨none,erased input ports⟩ (ticks input ports) peak := by
  induction ports generalizing input with
  | nil =>
    have transition : step (chain []) ⟨some (chain []).main,input⟩=some ⟨none,input⟩ := rfl
    exact ⟨_,Execution.cons transition (Execution.refl _)⟩
  | cons port rest ih =>
    obtain ⟨firstPeak,first⟩ := StackClear.ready_execution input port
    obtain ⟨restPeak,following⟩ := ih (Function.update input port [])
    exact ⟨max firstPeak restPeak,first.link following⟩

def ports : List Port := [none,some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,
  some 10,some 11,some 12,some 13,some 14,some 16,some 17,some 18,some 20,some 27,some 28,some 29,some 30]
def Label : Type := Labels ports
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (Labels ports))
def program : Program (Fin 31) Label := chain ports
def output (input : Port → List Bool) := erased input ports

theorem output_at (input : Port → List Bool) (port : Port) :
    output input port=if port ∈ ports then [] else input port := erased_at input ports port

theorem output_size (input : Port → List Bool) : FetchSetup.size (output input) ≤ FetchSetup.size input := by
  apply Finset.sum_le_sum
  intro port _
  rw [output_at]
  split <;> simp

theorem stored (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (r : NativeStore.Stored input state) : NativeStore.Stored (output input) state where
  widthStored := by simpa [output_at,ports] using r.widthStored
  countStored := by simpa [output_at,ports] using r.countStored
  registersStored := by simpa [output_at,ports] using r.registersStored
  heapStored := by simpa [output_at,ports] using r.heapStored
  stackStored := by simpa [output_at,ports] using r.stackStored
  outputStored := by simpa [output_at,ports] using r.outputStored
  pcStored := by simpa [output_at,ports] using r.pcStored
  haltStored := by simpa [output_at,ports] using r.haltStored

theorem ready (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (r : NativeStore.Stored input state) (running : state.halted=false)
    (code : input (some 19)=InstructionCodec.encodeMany bound instructions)
    (count : input (some 15)=List.replicate instructions.length true) :
    NativeStep.Ready (output input) state bound instructions where
  stored := stored input state r
  running := running
  codeStored := by simpa [output_at,ports] using code
  countStored := by simpa [output_at,ports] using count
  indexEmpty := by simp [output_at,ports]
  valueEmpty := by simp [output_at,ports]
  bufferEmpty := by simp [output_at,ports]
  resultEmpty := by simp [output_at,ports]
  clear := by
    intro port member
    have inclusion : FetchSetup.work ⊆ ports := by decide
    simp [output_at,inclusion member]
  extraClear := by simp [output_at,ports]

theorem execution (input : Port → List Bool) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input⟩ ticks peak ∧
      ticks ≤ FetchSetup.size input+45 ∧ peak ≤ 2*FetchSetup.size input+45 := by
  obtain ⟨peak,trace⟩ := chain_execution input ports
  have balance := mass_balance input ports
  have length : ports.length=22 := by decide
  rw [length] at balance
  have time : ticks input ports ≤ FetchSetup.size input+45 := by omega
  have space := trace.peak_le
  change peak ≤ FetchSetup.size input+ticks input ports at space
  exact ⟨_,peak,trace,time,by omega⟩

theorem labels_card (ports : List Port) : Fintype.card (Labels ports)=2*ports.length+1 := by
  induction ports with
  | nil => exact Fintype.card_fin 1
  | cons port rest ih =>
    change Fintype.card (Fin 2 ⊕ Labels rest)=_
    rw [Fintype.card_sum,Fintype.card_fin,ih]
    simp only [List.length_cons]
    omega

theorem canonical_card : Fintype.card Label=45 := labels_card ports

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 405 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.NativeReset
