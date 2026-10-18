module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.FieldGet
public import Controller.Complexity.InstructionCollect

@[expose] public section

/-! A finite routine replaces one persistent state field using a reversed
payload and an actual unary count. It erases the old field, moves the payload,
pushes its delimiter and consumes the count, preserving every other bank. -/
namespace Controller.Complexity.FieldCommit
open StackMachine StackBlocks WordReader
open scoped BigOperators

def fields (frame : Port → List Bool) (slot : Fin 5) (count : Nat) (packet buffer : List Bool) : Port → List Bool :=
  Function.update (Function.update (Function.update frame (some 10) (List.replicate count true)) (some 20) buffer) (some (FieldGet.field slot)) packet

theorem fields_at (frame : Port → List Bool) (slot : Fin 5) (count : Nat) (packet buffer : List Bool) (address : Port) :
    fields frame slot count packet buffer address=
      if address=some (FieldGet.field slot) then packet else if address=some 20 then buffer
      else if address=some 10 then List.replicate count true else frame address := by
  simp only [fields,Function.update_apply]

theorem update_packet (frame : Port → List Bool) (slot : Fin 5) (count : Nat) (packet buffer replacement : List Bool) :
    Function.update (fields frame slot count packet buffer) (some (FieldGet.field slot)) replacement=fields frame slot count replacement buffer := by
  funext address
  by_cases same : address=some (FieldGet.field slot) <;> simp_all [fields_at]

def delimiter (slot : Fin 5) : Program (Fin 31) (Fin 2) where
  main := 0
  code label := if label=0 then .push (some (FieldGet.field slot)) false 1 else .halt

def program (slot : Fin 5) :=
  link (link (link (StackClear.program (some (FieldGet.field slot) : Port))
    (transfer (some 20) (some (FieldGet.field slot)))) (delimiter slot)) (transfer (some 10) (some (FieldGet.field slot)))

theorem clear_execution (frame : Port → List Bool) (slot : Fin 5) (count : Nat) (packet buffer : List Bool) :
    ∃ peak, Execution (StackClear.program (some (FieldGet.field slot)))
      ⟨some (StackClear.program (some (FieldGet.field slot))).main,fields frame slot count packet buffer⟩
      ⟨none,fields frame slot count [] buffer⟩ (packet.length+2) peak := by
  obtain ⟨peak,trace⟩ := StackClear.ready_execution (fields frame slot count packet buffer) (some (FieldGet.field slot))
  exact ⟨peak,by simpa [fields_at,update_packet] using trace⟩

theorem payload_execution (frame : Port → List Bool) (slot : Fin 5) (count : Nat) (buffer : List Bool) :
    ∃ peak, Execution (transfer (some 20) (some (FieldGet.field slot)))
      ⟨some 0,fields frame slot count [] buffer⟩
      ⟨none,fields frame slot count buffer.reverse []⟩ (2*buffer.length+2) peak := by
  have distinct := (FieldGet.field_ne slot 20 (by decide)).symm
  obtain ⟨peak,trace⟩ := InstructionCollect.move_execution (fields frame slot count [] buffer) (some 20) (some (FieldGet.field slot)) distinct
  have output : Function.update (Function.update (fields frame slot count [] buffer) (some 20) []) (some (FieldGet.field slot))
      ((fields frame slot count [] buffer (some 20)).reverse++fields frame slot count [] buffer (some (FieldGet.field slot)))=
      fields frame slot count buffer.reverse [] := by
    funext address
    by_cases ht : address=some (FieldGet.field slot) <;> by_cases hb : address=some 20 <;>
      simp_all [fields_at,FieldGet.field_ne slot 20 (by decide)]
  rw [output] at trace
  exact ⟨peak,by simpa [fields_at,FieldGet.field_ne slot 20 (by decide),Ne.symm (FieldGet.field_ne slot 20 (by decide))] using trace⟩

theorem delimiter_execution (frame : Port → List Bool) (slot : Fin 5) (count : Nat) (packet : List Bool) :
    ∃ peak, Execution (delimiter slot) ⟨some (delimiter slot).main,fields frame slot count packet []⟩
      ⟨none,fields frame slot count (false :: packet) []⟩ 2 peak := by
  have first : step (delimiter slot) ⟨some (delimiter slot).main,fields frame slot count packet []⟩=
      some ⟨some 1,fields frame slot count (false :: packet) []⟩ := by
    simp [step,delimiter,instructionStep,fields_at,update_packet]
  have last : step (delimiter slot) ⟨some 1,fields frame slot count (false :: packet) []⟩=
      some ⟨none,fields frame slot count (false :: packet) []⟩ := rfl
  exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩

theorem count_execution (frame : Port → List Bool) (slot : Fin 5) (count : Nat) (packet : List Bool) :
    ∃ peak, Execution (transfer (some 10) (some (FieldGet.field slot)))
      ⟨some 0,fields frame slot count (false :: packet) []⟩
      ⟨none,fields frame slot 0 (Encoding.frameCount count packet) []⟩ (2*count+2) peak := by
  have distinct := (FieldGet.field_ne slot 10 (by decide)).symm
  obtain ⟨peak,trace⟩ := InstructionCollect.move_execution (fields frame slot count (false :: packet) []) (some 10) (some (FieldGet.field slot)) distinct
  have output : Function.update (Function.update (fields frame slot count (false :: packet) []) (some 10) []) (some (FieldGet.field slot))
      ((fields frame slot count (false :: packet) [] (some 10)).reverse++fields frame slot count (false :: packet) [] (some (FieldGet.field slot)))=
      fields frame slot 0 (Encoding.frameCount count packet) [] := by
    funext address
    by_cases ht : address=some (FieldGet.field slot) <;> by_cases hn : address=some 10 <;>
      simp_all [fields_at,Encoding.frameCount,FieldGet.field_ne slot 10 (by decide)]
  rw [output] at trace
  exact ⟨peak,by simpa [fields_at,FieldGet.field_ne slot 10 (by decide),Ne.symm (FieldGet.field_ne slot 10 (by decide))] using trace⟩

theorem execution (frame : Port → List Bool) (slot : Fin 5) (count : Nat) (packet buffer : List Bool) :
    ∃ peak, Execution (program slot) ⟨some (program slot).main,fields frame slot count packet buffer⟩
      ⟨none,fields frame slot 0 (Encoding.frameCount count buffer.reverse) []⟩
      (packet.length+2*buffer.length+2*count+8) peak := by
  obtain ⟨p₁,one⟩ := clear_execution frame slot count packet buffer
  obtain ⟨p₂,two⟩ := payload_execution frame slot count buffer
  obtain ⟨p₃,three⟩ := delimiter_execution frame slot count buffer.reverse
  obtain ⟨p₄,four⟩ := count_execution frame slot count buffer.reverse
  have trace := ((one.link two).link three).link four
  have ticks : ((packet.length+2)+(2*buffer.length+2))+2+(2*count+2)=packet.length+2*buffer.length+2*count+8 := by omega
  exact ⟨_,by simpa only [program,ticks] using trace⟩

theorem ready_execution (input : Port → List Bool) (slot : Fin 5) (count : Nat) (buffer : List Bool)
    (stored : input (some 10)=List.replicate count true) (saved : input (some 20)=buffer) :
    ∃ peak, Execution (program slot) ⟨some (program slot).main,input⟩
      ⟨none,fields input slot 0 (Encoding.frameCount count buffer.reverse) []⟩
      ((input (some (FieldGet.field slot))).length+2*buffer.length+2*count+8) peak := by
  have entry : fields input slot count (input (some (FieldGet.field slot))) buffer=input := by
    simp only [fields,← stored,← saved,Function.update_eq_self]
  simpa only [entry] using execution input slot count (input (some (FieldGet.field slot))) buffer

def size (input : Port → List Bool) : Nat := ∑ port : Port,(input port).length

theorem total_resources (input : Port → List Bool) (slot : Fin 5) (count : Nat) (buffer : List Bool)
    (stored : input (some 10)=List.replicate count true) (saved : input (some 20)=buffer) :
    ∃ ticks peak, Execution (program slot) ⟨some (program slot).main,input⟩
      ⟨none,fields input slot 0 (Encoding.frameCount count buffer.reverse) []⟩ ticks peak ∧
      ticks ≤ 5*size input+8 ∧ peak ≤ 6*size input+8 := by
  obtain ⟨peak,trace⟩ := ready_execution input slot count buffer stored saved
  have cell (port : Port) : (input port).length ≤ size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have countBound : count ≤ size input := by simpa only [stored,List.length_replicate] using cell (some 10)
  have bufferBound : buffer.length ≤ size input := by simpa only [saved] using cell (some 20)
  have packetBound := cell (some (FieldGet.field slot))
  have space := trace.peak_le
  change peak ≤ size input+_ at space
  exact ⟨_,peak,trace,by omega,by omega⟩

theorem resident (slot : Fin 5) : (∑ label, statementSize (tmStatement ((program slot).code label))) ≤ 108 := by
  simpa only [Fintype.card_sum,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident (program slot)

end Controller.Complexity.FieldCommit
