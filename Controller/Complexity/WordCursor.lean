module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.StackFrames

@[expose] public section

/-! A finite word cursor consumes a unary width counter and exactly that many
source bits, retaining the source suffix. The extracted bits are reversed onto
the destination. Premature end of input leaves an explicit false error marker
on the counter stack. -/
namespace Controller.Complexity.WordCursor
open StackMachine StackBlocks
open scoped BigOperators

def program : Program Bool (Fin 6) where
  main := 0
  code label := match label.val with
    | 0 => .pop none 4 1 1
    | 1 => .pop (some false) 5 2 3
    | 2 => .push (some true) false 0
    | 3 => .push (some true) true 0
    | 4 => .halt
    | _ => .push none false 4

def state (label : Option (Fin 6)) (counter source destination : List Bool) : State Bool (Fin 6) :=
  ⟨label, layout counter source destination⟩

def pending (bit : Bool) : Fin 6 := if bit then 3 else 2

theorem count_step (counter source destination : List Bool) :
    step program (state (some 0) (true :: counter) source destination) =
      some (state (some 1) counter source destination) := by
  simp [step, program, state, instructionStep, layout]
  funext stack
  cases stack with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem read_step (bit : Bool) (counter source destination : List Bool) :
    step program (state (some 1) counter (bit :: source) destination) =
      some (state (some (pending bit)) counter source destination) := by
  cases bit <;> simp [step, program, state, instructionStep, layout, pending]
  all_goals funext stack; cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl

theorem write_step (bit : Bool) (counter source destination : List Bool) :
    step program (state (some (pending bit)) counter source destination) =
      some (state (some 0) counter source (bit :: destination)) := by
  cases bit <;> simp [step, program, state, instructionStep, layout, pending]
  all_goals funext stack; cases stack with
    | none => rfl
    | some bit => cases bit <;> rfl

theorem done_step (source destination : List Bool) :
    step program (state (some 0) [] source destination) = some (state (some 4) [] source destination) := by
  simp [step, program, state, instructionStep, layout]

theorem halt_step (counter source destination : List Bool) :
    step program (state (some 4) counter source destination) = some (state none counter source destination) := rfl

theorem missing_step (counter destination : List Bool) :
    step program (state (some 1) counter [] destination) = some (state (some 5) counter [] destination) := by
  simp [step, program, state, instructionStep, layout]

theorem error_step (counter destination : List Bool) :
    step program (state (some 5) counter [] destination) = some (state (some 4) (false :: counter) [] destination) := by
  simp [step, program, state, instructionStep, layout]
  funext stack
  cases stack with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem execution (word suffix destination : List Bool) :
    Execution program (state (some 0) (List.replicate word.length true) (word ++ suffix) destination)
      (state none [] suffix (word.reverse ++ destination))
      (3*word.length+2) (2*word.length+suffix.length+destination.length) := by
  induction word generalizing destination with
  | nil =>
    have done := Execution.refl (program := program) (state none [] suffix destination)
    have trace := Execution.cons (done_step suffix destination) (Execution.cons (halt_step [] suffix destination) done)
    simpa [state, live_layout] using trace
  | cons bit word ih =>
    have tail := ih (bit :: destination)
    have one := Execution.cons (write_step bit (List.replicate word.length true) (word ++ suffix) destination) tail
    have two := Execution.cons (read_step bit (List.replicate word.length true) (word ++ suffix) destination) one
    have three := Execution.cons (count_step (List.replicate word.length true) (bit :: (word ++ suffix)) destination) two
    have count : ((3*word.length+2)+1)+1+1 = 3*(bit :: word).length+2 := by
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [count] at three
    have peak : max (live (state (some 0) (true :: List.replicate word.length true) (bit :: (word ++ suffix)) destination))
        (max (live (state (some 1) (List.replicate word.length true) (bit :: (word ++ suffix)) destination))
          (max (live (state (some (pending bit)) (List.replicate word.length true) (word ++ suffix) destination))
            (2*word.length+suffix.length+(bit :: destination).length))) =
        2*(bit :: word).length+suffix.length+destination.length := by
      simp only [state, live_layout, List.length_cons, List.length_replicate, List.length_append]
      omega
    rw [peak] at three
    simpa only [List.length_cons, List.replicate_succ, List.cons_append, List.reverse_cons,
      List.append_assoc, List.singleton_append, List.nil_append] using three

theorem short_execution (missing : Nat) (input destination : List Bool) :
    Execution program (state (some 0) (List.replicate (input.length+missing+1) true) input destination)
      (state none (false :: List.replicate missing true) [] (input.reverse ++ destination))
      (3*input.length+4) (2*input.length+missing+1+destination.length) := by
  induction input generalizing destination with
  | nil =>
    have done := Execution.refl (program := program) (state none (false :: List.replicate missing true) [] destination)
    have one := Execution.cons (halt_step (false :: List.replicate missing true) [] destination) done
    have two := Execution.cons (error_step (List.replicate missing true) destination) one
    have three := Execution.cons (missing_step (List.replicate missing true) destination) two
    have four := Execution.cons (count_step (List.replicate missing true) [] destination) three
    have peak : max (live (state (some 0) (true :: List.replicate missing true) [] destination))
        (max (live (state (some 1) (List.replicate missing true) [] destination))
          (max (live (state (some 5) (List.replicate missing true) [] destination))
            (max (live (state (some 4) (false :: List.replicate missing true) [] destination))
              (live (state none (false :: List.replicate missing true) [] destination))))) =
        missing+1+destination.length := by
      simp only [state, live_layout, List.length_cons, List.length_replicate, List.length_nil]
      omega
    rw [peak] at four
    simpa only [List.length_nil, Nat.zero_add, Nat.mul_zero, List.reverse_nil, List.nil_append, List.replicate_succ] using four
  | cons bit input ih =>
    have tail := ih (bit :: destination)
    have one := Execution.cons (write_step bit (List.replicate (input.length+missing+1) true) input destination) tail
    have two := Execution.cons (read_step bit (List.replicate (input.length+missing+1) true) input destination) one
    have three := Execution.cons (count_step (List.replicate (input.length+missing+1) true) (bit :: input) destination) two
    have count : ((3*input.length+4)+1)+1+1 = 3*(bit :: input).length+4 := by
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [count] at three
    have peak : max (live (state (some 0) (true :: List.replicate (input.length+missing+1) true) (bit :: input) destination))
        (max (live (state (some 1) (List.replicate (input.length+missing+1) true) (bit :: input) destination))
          (max (live (state (some (pending bit)) (List.replicate (input.length+missing+1) true) input destination))
            (2*input.length+missing+1+(bit :: destination).length))) =
        2*(bit :: input).length+missing+1+destination.length := by
      simp only [state, live_layout, List.length_cons, List.length_replicate]
      omega
    rw [peak] at three
    have header : (bit :: input).length+missing+1 = (input.length+missing+1)+1 := by simp [Nat.add_assoc, Nat.add_comm]
    simpa only [header, List.replicate_succ, List.reverse_cons, List.append_assoc, List.singleton_append] using three

theorem encoded_execution (width value : Nat) (suffix destination : List Bool) :
    Execution program (state (some 0) (List.replicate width true) (Encoding.bits width value ++ suffix) destination)
      (state none [] suffix ((Encoding.bits width value).reverse ++ destination))
      (3*width+2) (2*width+suffix.length+destination.length) := by
  simpa only [Encoding.bits_length] using execution (Encoding.bits width value) suffix destination

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 54 := by
  simpa using finiteTM_resident program

theorem framed_execution [Fintype K] [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (word suffix destination : List Bool) :
    Execution (StackFrames.relocate ports program)
      (StackFrames.embedState ports frame (state (some 0) (List.replicate word.length true) (word ++ suffix) destination))
      (StackFrames.embedState ports frame (state none [] suffix (word.reverse ++ destination)))
      (3*word.length+2) (2*word.length+suffix.length+destination.length+StackFrames.frameBits ports frame) :=
  StackFrames.execution ports frame (execution word suffix destination)

theorem framed_short_execution [Fintype K] [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (missing : Nat) (input destination : List Bool) :
    Execution (StackFrames.relocate ports program)
      (StackFrames.embedState ports frame (state (some 0) (List.replicate (input.length+missing+1) true) input destination))
      (StackFrames.embedState ports frame (state none (false :: List.replicate missing true) [] (input.reverse ++ destination)))
      (3*input.length+4) (2*input.length+missing+1+destination.length+StackFrames.frameBits ports frame) :=
  StackFrames.execution ports frame (short_execution missing input destination)

end Controller.Complexity.WordCursor
