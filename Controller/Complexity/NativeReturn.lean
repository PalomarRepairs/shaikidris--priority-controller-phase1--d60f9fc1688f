module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeReset

@[expose] public section

/-! The external return stage erases all thirty-one work banks and retains
the output stack. Its actual endpoint is the conventional terminal storage. -/
namespace Controller.Complexity.NativeReturn
open StackMachine WordReader
open scoped BigOperators

def ports : List Port := (List.finRange 31).map some
def Label : Type := NativeReset.Labels ports
instance labelFintype : Fintype Label := inferInstanceAs (Fintype (NativeReset.Labels ports))
def program : Program (Fin 31) Label := NativeReset.chain ports
def output (input : Port → List Bool) := NativeReset.erased input ports

theorem output_at (input : Port → List Bool) (port : Port) :
    output input port=match port with | none => input none | some _ => [] := by
  rw [output,NativeReset.erased_at]
  cases port with
  | none => simp [ports]
  | some index => simp [ports]

theorem terminal (input : Port → List Bool) :
    (⟨none,output input⟩ : State (Fin 31) Label)=StackMachine.terminal (input none) := by
  congr 1
  funext port
  cases port <;> simp [output_at]

theorem execution (input : Port → List Bool) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ (StackMachine.terminal (input none)) ticks peak ∧
      ticks ≤ FetchSetup.size input+63 ∧ peak ≤ 2*FetchSetup.size input+63 := by
  obtain ⟨peak,trace⟩ := NativeReset.chain_execution input ports
  have balance := NativeReset.mass_balance input ports
  have length : ports.length=31 := by decide
  rw [length] at balance
  have time : NativeReset.ticks input ports ≤ FetchSetup.size input+63 := by omega
  have space := trace.peak_le
  change peak ≤ FetchSetup.size input+NativeReset.ticks input ports at space
  change Execution program ⟨some program.main,input⟩ ⟨none,output input⟩ (NativeReset.ticks input ports) peak at trace
  rw [terminal] at trace
  exact ⟨_,peak,trace,time,by omega⟩

theorem canonical_card : Fintype.card Label=63 := by
  have card := NativeReset.labels_card ports
  exact card

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 567 := by
  have bound := finiteTM_resident program
  rw [canonical_card] at bound
  exact bound

end Controller.Complexity.NativeReturn
