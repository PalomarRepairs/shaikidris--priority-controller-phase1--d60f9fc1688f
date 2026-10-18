module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.NativeReset

@[expose] public section

/-! After the executed reset, physical live storage is exactly the ten
persistent packets. Its bound depends on actual native live words and encoded
program size, independently of scratch data left by an earlier cycle. -/
namespace Controller.Complexity.NativeEnvelope
open WordReader
open scoped BigOperators

def persistent : Finset Port := {some 8,some 9,some 15,some 19,some 21,some 22,some 23,some 24,some 25,some 26}

theorem partition : ∀ port : Port, port ∈ NativeReset.ports ↔ port ∉ persistent := by decide

theorem packet_sum (input : Port → List Bool) : FetchSetup.size (NativeReset.output input)=
    (input (some 8)).length+(input (some 9)).length+(input (some 15)).length+(input (some 19)).length+
    (input (some 21)).length+(input (some 22)).length+(input (some 23)).length+(input (some 24)).length+
    (input (some 25)).length+(input (some 26)).length := by
  have selected := Finset.sum_subset (f := fun port => (NativeReset.output input port).length)
    (Finset.subset_univ persistent) (by
      intro port _ outside
      simp [NativeReset.output_at,(partition port).2 outside])
  change (∑ port : Port, (NativeReset.output input port).length)=_
  rw [← selected]
  simp [persistent,NativeReset.output_at,NativeReset.ports]
  omega

def mass (width registers count bits nativeWords : Nat) := width+registers+count+bits+(width+1)*nativeWords+6

theorem size_eq (input : Port → List Bool) (state : Controller.Cost.State width registers)
    (bound : registers ≤ 2^width) (instructions : List (Controller.Cost.Instruction width registers))
    (stored : NativeStore.Stored input state)
    (code : input (some 19)=InstructionCodec.encodeMany bound instructions)
    (count : input (some 15)=List.replicate instructions.length true) :
    FetchSetup.size (NativeReset.output input)=mass width registers instructions.length
      (InstructionCodec.encodeMany bound instructions).length state.liveWords := by
  have native := congrArg List.length (stored.bytes input state)
  rw [MachineBridge.encodeState_length] at native
  simp only [StateNative.storedBytes,List.length_append] at native
  rw [packet_sum,stored.widthStored,stored.countStored,code,count]
  simp only [List.length_replicate,mass]
  omega

theorem mass_mono (width registers count bits : Nat) {first second : Nat} (bound : first ≤ second) :
    mass width registers count bits first ≤ mass width registers count bits second := by
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left (width+1) bound) _) _

theorem budget_mono {first second : Nat} (bound : first ≤ second) : NativeStep.budget first ≤ NativeStep.budget second := by
  unfold NativeStep.budget NativeStep.fetchBudget
  gcongr

end Controller.Complexity.NativeEnvelope
