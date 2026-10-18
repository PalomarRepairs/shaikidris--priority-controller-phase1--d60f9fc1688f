module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.RegisterRead
public import Controller.Complexity.NativeStore

@[expose] public section

/-! A fetched operand is loaded into either index3 or replacement27. The
old destination is actually erased and the returned word is moved in order;
all traversal workspace and every other bank are restored. -/
namespace Controller.Complexity.OperandLoad
open StackMachine WordReader
open scoped BigOperators

def destination (replacement : Bool) : Port := if replacement then some 27 else some 3

def program (position : Fin 3) (replacement : Bool) := link (link (RegisterRead.operandProgram position) (StackClear.program (destination replacement)))
  (WordMove.program (some 1) (destination replacement) (some 2))

def output (input : Port → List Bool) (replacement : Bool) (value : Controller.Cost.Word width) :=
  Function.update input (destination replacement) (Encoding.bits width value.val)

structure Ready (input : Port → List Bool) (operands : List (Controller.Cost.Word width)) : Prop where
  payload : input (some 11)=Encoding.wordList width operands
  stored : input (some 8)=List.replicate width true
  clear : ∀ port ∈ FieldSet.work, input port=[]

theorem update_size_le (input : Port → List Bool) (port : Port) (word : List Bool) :
    FetchSetup.size (Function.update input port word) ≤ FetchSetup.size input+word.length := by
  calc
    FetchSetup.size (Function.update input port word) ≤ ∑ address : Port, ((input address).length+if address=port then word.length else 0) := by
      apply Finset.sum_le_sum
      intro address _
      by_cases same : address=port <;> simp [same]
    _ = FetchSetup.size input+word.length := by simp [FetchSetup.size,Finset.sum_add_distrib]

theorem clear_output (input : Port → List Bool) (replacement : Bool) (value : Controller.Cost.Word width)
    (clean : ∀ port ∈ FieldSet.work, input port=[]) : ∀ port ∈ FieldSet.work, output input replacement value port=[] := by
  intro port member
  have outside : port ≠ destination replacement := by
    cases replacement <;> simp only [destination,Bool.false_eq_true,ite_false,ite_true] <;>
      intro equal <;> subst port <;> simp [FieldSet.work] at member
  simpa only [output,Function.update_of_ne outside] using clean port member

theorem stored_output (input : Port → List Bool) (replacement : Bool) (value : Controller.Cost.Word width)
    (state : Controller.Cost.State width registers) (stored : NativeStore.Stored input state) :
    NativeStore.Stored (output input replacement value) state := by
  apply stored.update_other input state (destination replacement) (Encoding.bits width value.val)
  cases replacement <;> decide

theorem payload_output (input : Port → List Bool) (replacement : Bool) (value : Controller.Cost.Word width) :
    output input replacement value (some 11)=input (some 11) := by cases replacement <;> simp [output,destination]

theorem execution (input : Port → List Bool) (operands : List (Controller.Cost.Word width)) (position : Fin 3) (replacement : Bool)
    (valid : position.val<operands.length) (ready : Ready input operands) :
    ∃ ticks peak, Execution (program position replacement) ⟨some (program position replacement).main,input⟩
      ⟨none,output input replacement operands[position.val]⟩ ticks peak ∧
      ticks ≤ 55*FetchSetup.size input+59 ∧ peak ≤ 56*FetchSetup.size input+59 := by
  have notWord : destination replacement ≠ (some 1 : Port) := by cases replacement <;> decide
  have notScratch : destination replacement ≠ (some 2 : Port) := by cases replacement <;> decide
  obtain ⟨readTicks,readPeak,reading,readBound,_⟩ := OperandRead.encoded_total input operands position valid ready.payload ready.stored
    (by
      intro port member
      apply ready.clear port
      simp only [OperandRead.work,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl <;> simp [FieldSet.work])
  let word := Encoding.bits width operands[position.val].val
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (Function.update input (some 1) word) (destination replacement)
  simp only [Function.update_of_ne notWord] at clearing
  obtain ⟨movePeak,moving⟩ := WordMove.execution (Function.update (Function.update input (some 1) word) (destination replacement) [])
    (some 1) (destination replacement) (some 2) notWord.symm (by decide) notScratch
    (by simpa [Function.update_of_ne notScratch.symm] using ready.clear (some 2) (by simp [FieldSet.work]))
  simp only [Function.update_self,Function.update_of_ne notWord.symm,List.append_nil] at moving
  have final : Function.update (Function.update (Function.update (Function.update input (some 1) word) (destination replacement) []) (some 1) [])
      (destination replacement) word=output input replacement operands[position.val] := by
    funext address
    have empty := ready.clear (some 1) (by simp [FieldSet.work])
    by_cases hw : address=some 1 <;> by_cases hd : address=destination replacement <;> simp_all [output,word]
  rw [final] at moving
  simp only [word,Encoding.bits_length] at moving
  have trace := (reading.link clearing).link moving
  have cell (port : Port) : (input port).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored,List.length_replicate] using cell (some 8)
  change readTicks ≤ 50*FetchSetup.size input+53 at readBound
  have timeBound : (readTicks+((input (destination replacement)).length+2))+(4*width+4) ≤ 55*FetchSetup.size input+59 := by
    have destinationBound := cell (destination replacement)
    omega
  have space := trace.peak_le
  change max (max readPeak clearPeak) movePeak ≤ FetchSetup.size input+((readTicks+((input (destination replacement)).length+2))+(4*width+4)) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem canonical_card : Fintype.card (StateReader.LabelsOf (program position replacement))=88 := by
  simp only [StateReader.LabelsOf,Fintype.card_sum,RegisterRead.operand_card,Fintype.card_fin,Nat.reduceAdd]

theorem resident (position : Fin 3) (replacement : Bool) :
    (∑ label, statementSize (tmStatement ((program position replacement).code label))) ≤ 792 := by
  have bound := finiteTM_resident (program position replacement)
  rw [show Fintype.card (StateReader.LabelsOf (program position replacement))=88 from canonical_card] at bound
  exact bound

end Controller.Complexity.OperandLoad
