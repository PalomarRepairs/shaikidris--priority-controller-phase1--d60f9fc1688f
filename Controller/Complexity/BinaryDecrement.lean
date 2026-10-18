module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.BinaryIncrement

@[expose] public section

/-! Executed binary decrement with canonical high-bit removal. A borrowed low
zero is saved as a low one in scratch and restored after the borrow ends.
Canonical zero remains zero. Arbitrary lists use the literal borrow rule;
an all-zero nonempty list wraps to ones. Input and output are unchanged. -/
namespace Controller.Complexity.BinaryDecrement
open SpaceMachine

def decrement : List Bool → List Bool
  | [] => []
  | false :: rest => true :: decrement rest
  | true :: rest => if rest=[] then [] else false :: rest

def cost : List Bool → Nat
  | [] => 3
  | false :: rest => cost rest+4
  | true :: rest => if rest=[] then 4 else 5

theorem cost_le (bits : List Bool) : cost bits ≤ 4*bits.length+3 := by
  induction bits with
  | nil => decide
  | cons bit rest ih =>
    cases bit with
    | false => simp only [cost,List.length_cons]; omega
    | true =>
      cases rest <;> simp only [cost,List.length_cons,List.length_nil,List.cons_ne_nil,ite_true,ite_false] <;> omega

theorem decrement_bits (number : Nat) : decrement number.bits=(number-1).bits := by
  induction number using Nat.binaryRec' with
  | zero => simp [decrement]
  | bit bit number valid ih =>
    rw [Nat.bits_append_bit number bit valid]
    cases bit with
    | false =>
      have nonzero : number ≠ 0 := by intro zero; simpa using valid zero
      have shape : Nat.bit false number-1=2*(number-1)+1 := by
        simp only [Nat.bit,Bool.cond_false]
        omega
      rw [decrement,ih,shape,Nat.bit1_bits]
    | true =>
      by_cases zero : number=0
      · subst number
        simp [decrement,Nat.bit]
      · have nonempty : number.bits ≠ [] := by
          intro empty
          have length := Nat.size_eq_bits_len number
          rw [empty,List.length_nil] at length
          exact zero (Nat.size_eq_zero.mp length.symm)
        have shape : Nat.bit true number-1=2*number := by simp [Nat.bit]
        rw [decrement,ite_eq_right nonempty,shape,Nat.bit0_bits number zero]

def program : SpaceMachine.Program Bool (Fin 7) where
  main := 0
  code label := match label.val with
    | 0 => .pop false 4 3 1
    | 1 => .peek false 4 2 2
    | 2 => .push false false 4
    | 3 => .push true true 0
    | 4 => .pop true 6 5 5
    | 5 => .push false true 4
    | _ => .halt

abbrev state := BinaryIncrement.state

theorem restore_empty (tape : ReadOnlyInput.Tape) (output bits : List Bool) :
    step program (state tape output (some 4) bits [])=some (state tape output (some 6) bits []) := by
  simp [step,program,BinaryIncrement.state,instructionStep,advance,observed,BinaryIncrement.update_true]

theorem restore_pop (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 4) bits (true :: scratch))=some (state tape output (some 5) bits scratch) := by
  simp [step,program,BinaryIncrement.state,instructionStep,advance,observed,BinaryIncrement.update_true]

theorem restore_push (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 5) bits scratch)=some (state tape output (some 4) (true :: bits) scratch) := by
  simp [step,program,BinaryIncrement.state,instructionStep,advance,BinaryIncrement.update_false]

theorem halt_step (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 6) bits scratch)=some (state tape output none bits scratch) := rfl

theorem restore_execution (tape : ReadOnlyInput.Tape) (output bits : List Bool) (count : Nat) :
    SpaceMachine.Execution program (state tape output (some 4) bits (List.replicate count true))
      (state tape output none (List.replicate count true++bits) []) (2*count+2) (bits.length+count) := by
  induction count generalizing bits with
  | zero =>
    have trace := Execution.cons (restore_empty tape output bits)
      (Execution.cons (halt_step tape output bits []) (Execution.refl _))
    simpa only [List.replicate_zero,List.nil_append,BinaryIncrement.state_workspace,List.length_nil,
      Nat.add_zero,Nat.max_self] using trace
  | succ count ih =>
    have trace := Execution.cons (restore_pop tape output bits (List.replicate count true))
      (Execution.cons (restore_push tape output bits (List.replicate count true)) (ih (true :: bits)))
    have result : List.replicate count true++true :: bits=List.replicate (count+1) true++bits := by
      rw [List.replicate_succ']
      simp only [List.append_assoc,List.singleton_append]
    rw [result] at trace
    convert trace using 1 <;>
      first
      | rfl
      | (simp only [BinaryIncrement.state_workspace,List.length_replicate,List.length_cons]; omega)

theorem pop_empty (tape : ReadOnlyInput.Tape) (output scratch : List Bool) :
    step program (state tape output (some 0) [] scratch)=some (state tape output (some 4) [] scratch) := by
  simp [step,program,BinaryIncrement.state,instructionStep,advance,observed,BinaryIncrement.update_false]

theorem pop_zero (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 0) (false :: bits) scratch)=some (state tape output (some 3) bits scratch) := by
  simp [step,program,BinaryIncrement.state,instructionStep,advance,observed,BinaryIncrement.update_false]

theorem pop_one (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 0) (true :: bits) scratch)=some (state tape output (some 1) bits scratch) := by
  simp [step,program,BinaryIncrement.state,instructionStep,advance,observed,BinaryIncrement.update_false]

theorem borrow_push (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 3) bits scratch)=some (state tape output (some 0) bits (true :: scratch)) := by
  simp [step,program,BinaryIncrement.state,instructionStep,advance,BinaryIncrement.update_true]

theorem high_empty (tape : ReadOnlyInput.Tape) (output scratch : List Bool) :
    step program (state tape output (some 1) [] scratch)=some (state tape output (some 4) [] scratch) := rfl

theorem high_nonempty (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) (bit : Bool) :
    step program (state tape output (some 1) (bit :: bits) scratch)=some (state tape output (some 2) (bit :: bits) scratch) := by
  cases bit <;> rfl

theorem high_zero (tape : ReadOnlyInput.Tape) (output bits scratch : List Bool) :
    step program (state tape output (some 2) bits scratch)=some (state tape output (some 4) (false :: bits) scratch) := by
  simp [step,program,BinaryIncrement.state,instructionStep,advance,BinaryIncrement.update_false]

theorem borrow_execution (tape : ReadOnlyInput.Tape) (output bits : List Bool) (count : Nat) :
    SpaceMachine.Execution program (state tape output (some 0) bits (List.replicate count true))
      (state tape output none (List.replicate count true++decrement bits) [])
      (cost bits+2*count) (bits.length+count) := by
  induction bits generalizing count with
  | nil =>
    have trace := Execution.cons (pop_empty tape output (List.replicate count true))
      (restore_execution tape output [] count)
    convert trace using 1 <;>
      simp only [cost,decrement,BinaryIncrement.state_workspace,List.length_nil,List.length_replicate] <;> omega
  | cons bit bits ih =>
    cases bit with
    | false =>
      have trace := Execution.cons (pop_zero tape output bits (List.replicate count true))
        (Execution.cons (borrow_push tape output bits (List.replicate count true)) (ih (count+1)))
      have result : List.replicate (count+1) true++decrement bits=List.replicate count true++true :: decrement bits := by
        rw [List.replicate_succ']
        simp only [List.append_assoc,List.singleton_append]
      rw [result] at trace
      convert trace using 1 <;>
        simp only [cost,decrement,BinaryIncrement.state_workspace,List.length_cons,List.length_replicate] <;> omega
    | true =>
      cases bits with
      | nil =>
        have trace := Execution.cons (pop_one tape output [] (List.replicate count true))
          (Execution.cons (high_empty tape output (List.replicate count true)) (restore_execution tape output [] count))
        convert trace using 1 <;>
          simp only [cost,decrement,ite_true,BinaryIncrement.state_workspace,List.length_cons,List.length_nil,
            List.length_replicate] <;> omega
      | cons high rest =>
        have trace := Execution.cons (pop_one tape output (high :: rest) (List.replicate count true))
          (Execution.cons (high_nonempty tape output rest (List.replicate count true) high)
            (Execution.cons (high_zero tape output (high :: rest) (List.replicate count true))
              (restore_execution tape output (false :: high :: rest) count)))
        simp only [cost,decrement,List.cons_ne_nil,ite_false,BinaryIncrement.state_workspace,List.length_cons,List.length_replicate] at *
        convert trace using 1 <;> omega

theorem execution (tape : ReadOnlyInput.Tape) (output bits : List Bool) :
    SpaceMachine.Execution program (state tape output (some program.main) bits [])
      (state tape output none (decrement bits) []) (cost bits) bits.length := by
  simpa only [program,List.replicate_zero,List.nil_append,Nat.mul_zero,Nat.add_zero] using borrow_execution tape output bits 0

theorem encoded_execution (tape : ReadOnlyInput.Tape) (output : List Bool) (number : Nat) :
    ∃ ticks, SpaceMachine.Execution program (state tape output (some program.main) number.bits [])
      (state tape output none (number-1).bits []) ticks number.bits.length ∧
      ticks ≤ 4*(Nat.log 2 (number+2)+1)+3 := by
  have trace := execution tape output number.bits
  rw [decrement_bits] at trace
  have time := cost_le number.bits
  have length := BinaryIncrement.counter_length number
  exact ⟨_,trace,by omega⟩

end Controller.Complexity.BinaryDecrement
