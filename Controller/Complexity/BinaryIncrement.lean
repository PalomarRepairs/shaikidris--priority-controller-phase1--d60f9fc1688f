module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.SpaceTM
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.Log

@[expose] public section

/-! An executed unbounded binary increment. Carry bits move through an empty
scratch bank and return as low zero bits; the input tape and output history
are unchanged. Canonical natural-number counters remain logarithmic in value. -/
namespace Controller.Complexity.BinaryIncrement
open SpaceMachine

def increment : List Bool → List Bool
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => false :: increment rest

def carries : List Bool → Nat
  | true :: rest => carries rest+1
  | _ => 0

theorem carries_le (bits : List Bool) : carries bits ≤ bits.length := by
  induction bits with
  | nil => decide
  | cons bit rest ih =>
    cases bit with
    | false => simp [carries]
    | true => simp only [carries,List.length_cons]; omega

theorem increment_length (bits : List Bool) : (increment bits).length ≤ bits.length+1 := by
  induction bits with
  | nil => decide
  | cons bit rest ih =>
    cases bit with
    | false => simp [increment]
    | true => simp only [increment,List.length_cons]; omega

theorem increment_bits (number : Nat) : increment number.bits=(number+1).bits := by
  induction number using Nat.binaryRec' with
  | zero => simp [increment]
  | bit bit number valid ih =>
    rw [Nat.bits_append_bit number bit valid]
    cases bit with
    | false => simp [increment,Nat.bit]
    | true =>
      have nonzero : number+1 ≠ 0 := by omega
      have even : Nat.bit true number+1=2*(number+1) := by simp [Nat.bit]; omega
      rw [increment,ih,even,Nat.bit0_bits _ nonzero]

theorem counter_length (number : Nat) : number.bits.length ≤ Nat.log 2 (number+2)+1 := by
  rw [Nat.size_eq_bits_len,Nat.size_le]
  exact (Nat.le_add_right number 2).trans_lt (Nat.lt_pow_succ_log_self (by decide) (number+2))

def program : SpaceMachine.Program Bool (Fin 7) where
  main := 0
  code label := match label.val with
    | 0 => .pop false 1 2 3
    | 1 => .push false true 4
    | 2 => .push false true 4
    | 3 => .push true false 0
    | 4 => .pop true 6 5 5
    | 5 => .push false false 4
    | _ => .halt

def work (bits scratch : List Bool) : Bool → List Bool
  | false => bits
  | true => scratch

def state (tape : ReadOnlyInput.Tape) (output : List Bool) (pc : Option (Fin 7)) (bits scratch : List Bool) :
    SpaceMachine.State Bool (Fin 7) := ⟨pc,tape,work bits scratch,output⟩

@[simp] theorem work_at_false (bits scratch : List Bool) : work bits scratch false=bits := rfl
@[simp] theorem work_at_true (bits scratch : List Bool) : work bits scratch true=scratch := rfl

@[simp] theorem work_nil : work [] []=(fun _ => []) := by
  funext port
  cases port <;> rfl

theorem update_false (bits scratch replacement : List Bool) :
    Function.update (work bits scratch) false replacement=work replacement scratch := by
  funext port
  cases port <;> rfl

theorem update_true (bits scratch replacement : List Bool) :
    Function.update (work bits scratch) true replacement=work bits replacement := by
  funext port
  cases port <;> rfl

theorem state_workspace (tape : ReadOnlyInput.Tape) (output : List Bool) (pc : Option (Fin 7)) (bits scratch : List Bool) :
    workspace (state tape output pc bits scratch)=bits.length+scratch.length := by
  simp [workspace,state,work,Nat.add_comm]

theorem restore_empty (tape : ReadOnlyInput.Tape) (output bits : List Bool) :
    step program (state tape output (some 4) bits [])=some (state tape output (some 6) bits []) := by
  simp [step,program,state,instructionStep,advance,observed,update_true]

theorem restore_pop (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 4) bits (false :: scratch))=some (state tape output (some 5) bits scratch) := by
  simp [step,program,state,instructionStep,advance,observed,update_true]

theorem restore_push (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 5) bits scratch)=some (state tape output (some 4) (false :: bits) scratch) := by
  simp [step,program,state,instructionStep,advance,update_false]

theorem halt_step (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 6) bits scratch)=some (state tape output none bits scratch) := rfl

theorem restore_execution (tape : ReadOnlyInput.Tape) (output bits : List Bool) (count : Nat) :
    ∃ peak, SpaceMachine.Execution program (state tape output (some 4) bits (List.replicate count false))
      (state tape output none (List.replicate count false++bits) []) (2*count+2) peak ∧ peak ≤ bits.length+count := by
  induction count generalizing bits with
  | zero =>
    have trace := Execution.cons (restore_empty tape output bits)
      (Execution.cons (halt_step tape output bits []) (Execution.refl _))
    refine ⟨bits.length,?_,by omega⟩
    simpa only [List.replicate_zero,List.nil_append,state_workspace,List.length_nil,Nat.add_zero,Nat.max_self] using trace
  | succ count ih =>
    obtain ⟨peak,tail,bounded⟩ := ih (false :: bits)
    have trace := Execution.cons (restore_pop tape output bits (List.replicate count false))
      (Execution.cons (restore_push tape output bits (List.replicate count false)) tail)
    have result : List.replicate count false++false :: bits=List.replicate (count+1) false++bits := by
      rw [List.replicate_succ']
      simp only [List.append_assoc,List.singleton_append]
    rw [result] at trace
    refine ⟨max (bits.length+(count+1)) (max (bits.length+count) peak),?_,?_⟩
    · simpa only [List.replicate_succ,Nat.mul_add,Nat.mul_one,Nat.add_assoc,state_workspace,List.length_cons,List.length_replicate] using trace
    · simp only [state_workspace,List.length_cons,List.length_replicate] at *
      omega

theorem pop_empty (tape : ReadOnlyInput.Tape) (output scratch : List Bool) :
    step program (state tape output (some 0) [] scratch)=some (state tape output (some 1) [] scratch) := by
  simp [step,program,state,instructionStep,advance,observed,update_false]

theorem pop_false (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 0) (false :: bits) scratch)=some (state tape output (some 2) bits scratch) := by
  simp [step,program,state,instructionStep,advance,observed,update_false]

theorem pop_true (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 0) (true :: bits) scratch)=some (state tape output (some 3) bits scratch) := by
  simp [step,program,state,instructionStep,advance,observed,update_false]

theorem end_carry (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) (label : Fin 7)
    (allowed : label=1 ∨ label=2) :
    step program (state tape output (some label) bits scratch)=some (state tape output (some 4) (true :: bits) scratch) := by
  rcases allowed with rfl | rfl <;> simp [step,program,state,instructionStep,advance,update_false]

theorem carry_push (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 3) bits scratch)=some (state tape output (some 0) bits (false :: scratch)) := by
  simp [step,program,state,instructionStep,advance,update_true]

theorem carry_execution (tape : ReadOnlyInput.Tape) (output bits : List Bool) (count : Nat) :
    ∃ peak, SpaceMachine.Execution program (state tape output (some 0) bits (List.replicate count false))
      (state tape output none (List.replicate count false++increment bits) [])
      (4*carries bits+2*count+4) peak ∧ peak ≤ bits.length+count+1 := by
  induction bits generalizing count with
  | nil =>
    obtain ⟨peak,tail,bounded⟩ := restore_execution tape output [true] count
    have trace := Execution.cons (pop_empty tape output (List.replicate count false))
      (Execution.cons (end_carry tape output [] (List.replicate count false) 1 (Or.inl rfl)) tail)
    refine ⟨max count (max count peak),?_,?_⟩
    · simpa only [increment,carries,Nat.mul_zero,Nat.zero_add,Nat.add_assoc,state_workspace,List.length_nil,List.length_replicate] using trace
    · simp only [state_workspace,List.length_nil,List.length_cons,List.length_replicate,Nat.zero_add] at *
      omega
  | cons bit bits ih =>
    cases bit with
    | false =>
      obtain ⟨peak,tail,bounded⟩ := restore_execution tape output (true :: bits) count
      have trace := Execution.cons (pop_false tape output bits (List.replicate count false))
        (Execution.cons (end_carry tape output bits (List.replicate count false) 2 (Or.inr rfl)) tail)
      refine ⟨max ((bits.length+1)+count) (max (bits.length+count) peak),?_,?_⟩
      · simpa only [increment,carries,Nat.mul_zero,Nat.zero_add,Nat.add_assoc,state_workspace,List.length_cons,List.length_replicate] using trace
      · simp only [state_workspace,List.length_cons,List.length_replicate] at *
        omega
    | true =>
      obtain ⟨peak,tail,bounded⟩ := ih (count+1)
      have trace := Execution.cons (pop_true tape output bits (List.replicate count false))
        (Execution.cons (carry_push tape output bits (List.replicate count false)) tail)
      have result : List.replicate (count+1) false++increment bits=
          List.replicate count false++false :: increment bits := by
        rw [List.replicate_succ']
        simp only [List.append_assoc,List.singleton_append]
      rw [result] at trace
      have clock : 4*carries bits+2*(count+1)+4+1+1=4*(carries bits+1)+2*count+4 := by omega
      rw [clock] at trace
      refine ⟨max ((bits.length+1)+count) (max (bits.length+count) peak),?_,?_⟩
      · simpa only [increment,carries,List.replicate_succ,state_workspace,List.length_cons,List.length_replicate] using trace
      · simp only [state_workspace,List.length_cons,List.length_replicate] at *
        omega

theorem execution (tape : ReadOnlyInput.Tape) (output bits : List Bool) :
    ∃ ticks peak, SpaceMachine.Execution program (state tape output (some program.main) bits [])
      (state tape output none (increment bits) []) ticks peak ∧
      ticks=4*carries bits+4 ∧ ticks ≤ 4*bits.length+4 ∧ peak ≤ bits.length+1 := by
  obtain ⟨peak,trace,bounded⟩ := carry_execution tape output bits 0
  have carriesBound := carries_le bits
  exact ⟨_,peak,by simpa only [program,List.replicate_zero,List.nil_append,Nat.mul_zero,Nat.add_zero] using trace,
    by omega,by omega,by simpa only [Nat.add_zero] using bounded⟩

theorem encoded_execution (tape : ReadOnlyInput.Tape) (output : List Bool) (number : Nat) :
    ∃ ticks peak, SpaceMachine.Execution program (state tape output (some program.main) number.bits [])
      (state tape output none (number+1).bits []) ticks peak ∧
      ticks ≤ 4*(Nat.log 2 (number+2)+1)+4 ∧ peak ≤ Nat.log 2 (number+2)+2 := by
  obtain ⟨ticks,peak,trace,_,time,space⟩ := execution tape output number.bits
  rw [increment_bits] at trace
  have length := counter_length number
  exact ⟨ticks,peak,trace,by omega,by omega⟩

end Controller.Complexity.BinaryIncrement
