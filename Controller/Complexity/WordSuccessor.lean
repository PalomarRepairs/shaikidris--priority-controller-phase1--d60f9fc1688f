module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordMove
public import Controller.Complexity.InstructionFrontend

@[expose] public section

/-! A fixed finite binary successor consumes its little-endian source, drops
final overflow and returns little-endian output after an executed reversal.
The routine covers width zero and uses no integer-sized unary counter. -/
namespace Controller.Complexity.WordSuccessor
open StackMachine StackBlocks
open scoped BigOperators

def carryBits (carry : Bool) : List Bool → List Bool
  | [] => []
  | bit :: rest => (bit ^^ carry) :: carryBits (bit && carry) rest

theorem carryBits_length (carry : Bool) (word : List Bool) : (carryBits carry word).length=word.length := by
  induction word generalizing carry with
  | nil => rfl
  | cons bit word ih => simp only [carryBits,List.length_cons,ih]

theorem carryBits_addBits (carry : Bool) (word : List Bool) :
    carryBits carry word=WordArithmetic.addBits carry word (List.replicate word.length false) := by
  induction word generalizing carry with
  | nil => rfl
  | cons bit word ih => cases bit <;> cases carry <;>
      simp [carryBits,WordArithmetic.addBits,List.replicate_succ,WordArithmetic.sumBit,WordArithmetic.carryBit,ih]

theorem zero_bits (width : Nat) : Encoding.bits width 0=List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih => simp [Encoding.bits,ih,List.replicate_succ]

theorem encoded_carry (carry : Bool) (width number : Nat) :
    carryBits carry (Encoding.bits width number)=Encoding.bits width (number+(if carry then 1 else 0)) := by
  rw [carryBits_addBits,Encoding.bits_length,← zero_bits]
  simpa only [Nat.add_zero] using WordArithmetic.addBits_bits carry width number 0

theorem native_bits (width number : Nat) :
    carryBits true (Encoding.bits width number)=Encoding.bits width (Controller.Cost.word width (number+1)).val := by
  have canonical := InstructionFrontend.bits_value (Encoding.bits width (number+1))
  rw [Encoding.bits_length,WordArithmetic.value_bits_mod] at canonical
  simpa only [encoded_carry,ite_true,Controller.Cost.word] using canonical.symm

def entry (carry : Bool) : Fin 7 := if carry then 0 else 3

def pending (bit carry : Bool) : Fin 7 := if carry then (if bit then 2 else 1) else (if bit then 5 else 4)

def core : Program Bool (Fin 7) where
  main := entry true
  code label := match label.val with
    | 0 => .pop none 6 1 2
    | 1 => .push (some false) true 3
    | 2 => .push (some false) false 0
    | 3 => .pop none 6 4 5
    | 4 => .push (some false) false 3
    | 5 => .push (some false) true 3
    | _ => .halt

def state (label : Option (Fin 7)) (word output : List Bool) : State Bool (Fin 7) := ⟨label,layout word output []⟩

theorem source_update (word output replacement : List Bool) : Function.update (layout word output []) none replacement=layout replacement output [] := by
  funext port
  cases port with
  | none => simp [layout]
  | some bit => cases bit <;> simp [layout]

theorem output_update (word output replacement : List Bool) : Function.update (layout word output []) (some false) replacement=layout word replacement [] := by
  funext port
  cases port with
  | none => simp [layout]
  | some bit => cases bit <;> simp [layout]

theorem pop_step (carry bit : Bool) (word output : List Bool) :
    step core (state (some (entry carry)) (bit :: word) output)=some (state (some (pending bit carry)) word output) := by
  cases carry <;> cases bit <;> simp [step,core,entry,pending,state,instructionStep,layout,source_update]

theorem push_step (carry bit : Bool) (word output : List Bool) :
    step core (state (some (pending bit carry)) word output)=some (state (some (entry (bit && carry))) word ((bit ^^ carry) :: output)) := by
  cases carry <;> cases bit <;> simp [step,core,entry,pending,state,instructionStep,layout,output_update]

theorem core_execution (carry : Bool) (word output : List Bool) :
    ∃ peak, Execution core (state (some (entry carry)) word output)
      (state none [] ((carryBits carry word).reverse++output)) (2*word.length+2) peak := by
  induction word generalizing carry output with
  | nil =>
    have first : step core (state (some (entry carry)) [] output)=some (state (some 6) [] output) := by
      cases carry <;> simp [step,core,entry,state,instructionStep,layout,source_update]
    have last : step core (state (some 6) [] output)=some (state none [] output) := rfl
    exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩
  | cons bit word ih =>
    obtain ⟨peak,tail⟩ := ih (bit && carry) ((bit ^^ carry) :: output)
    have trace := Execution.cons (pop_step carry bit word output) (Execution.cons (push_step carry bit word output) tail)
    have ticks : (2*word.length+2)+1+1=2*(bit :: word).length+2 := by simp only [List.length_cons]; omega
    exact ⟨_,by simpa only [ticks,carryBits,List.reverse_cons,List.singleton_append,List.append_assoc] using trace⟩

def reversePorts : Option Bool ↪ Option Bool := StackFrames.threePorts (some false) none (some true) (by decide) (by decide) (by decide)
theorem reversePorts_apply (port : Option Bool) : reversePorts port=(match port with | none => some false | some false => none | some true => some true) := rfl

def reverseMachine := StackFrames.relocate reversePorts reverseProgram

theorem reverse_storage (word temporary scratch : List Bool) :
    StackFrames.embedStorage reversePorts (layout [] [] []) (layout word temporary scratch)=layout temporary word scratch := by
  funext port
  cases port with
  | none => simp [StackFrames.embedStorage,reversePorts_apply,layout]
  | some bit => cases bit <;> simp [StackFrames.embedStorage,reversePorts_apply,layout]

theorem reverse_execution (word : List Bool) :
    ∃ peak, Execution reverseMachine ⟨some reverseMachine.main,layout [] word []⟩
      ⟨none,layout [] word.reverse []⟩ (6*word.length+6) peak := by
  have trace := StackFrames.reversal reversePorts (layout [] [] []) word
  exact ⟨_,by simpa only [reverseMachine,StackFrames.relocate,StackFrames.embedState,initial_layout,terminal_layout,reverse_storage] using trace⟩

def program := link core reverseMachine

theorem execution (word : List Bool) :
    ∃ peak, Execution program ⟨some program.main,layout word [] []⟩
      ⟨none,layout [] (carryBits true word) []⟩ (8*word.length+8) peak := by
  obtain ⟨corePeak,calculating⟩ := core_execution true word []
  simp only [List.append_nil] at calculating
  obtain ⟨reversePeak,reversing⟩ := reverse_execution (carryBits true word).reverse
  simp only [List.reverse_reverse,List.length_reverse,carryBits_length] at reversing
  have trace := calculating.link reversing
  have ticks : (2*word.length+2)+(6*word.length+6)=8*word.length+8 := by omega
  exact ⟨_,by simpa only [program,state,ticks] using trace⟩

theorem encoded_execution (width number : Nat) :
    ∃ peak, Execution program ⟨some program.main,layout (Encoding.bits width number) [] []⟩
      ⟨none,layout [] (Encoding.bits width (Controller.Cost.word width (number+1)).val) []⟩ (8*width+8) peak := by
  simpa only [native_bits,Encoding.bits_length] using execution (Encoding.bits width number)

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 171 := by
  simpa only [Fintype.card_sum,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.WordSuccessor
