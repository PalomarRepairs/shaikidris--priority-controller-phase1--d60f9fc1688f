module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.StackFrames
public import Controller.Complexity.GuardedLink

@[expose] public section

/-! A fixed finite parser for unary count-delimited headers. Success consumes
the false delimiter and retains the payload. End of input before the delimiter
leaves a false error marker on the unary counter. -/
namespace Controller.Complexity.HeaderParser
open StackMachine StackBlocks
open scoped BigOperators

def program : Program Bool (Fin 4) where
  main := 0
  code label := match label.val with
    | 0 => .pop none 3 2 1
    | 1 => .push (some false) true 0
    | 2 => .halt
    | _ => .push (some false) false 2

def state (label : Option (Fin 4)) (source counter scratch : List Bool) : State Bool (Fin 4) :=
  ⟨label, layout source counter scratch⟩

theorem true_step (source counter scratch : List Bool) :
    step program (state (some 0) (true :: source) counter scratch) = some (state (some 1) source counter scratch) := by
  simp [step, program, state, instructionStep, layout]
  funext port
  cases port with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem push_step (source counter scratch : List Bool) :
    step program (state (some 1) source counter scratch) = some (state (some 0) source (true :: counter) scratch) := by
  simp [step, program, state, instructionStep, layout]
  funext port
  cases port with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem false_step (source counter scratch : List Bool) :
    step program (state (some 0) (false :: source) counter scratch) = some (state (some 2) source counter scratch) := by
  simp [step, program, state, instructionStep, layout]
  funext port
  cases port with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem empty_step (counter scratch : List Bool) :
    step program (state (some 0) [] counter scratch) = some (state (some 3) [] counter scratch) := by
  simp [step, program, state, instructionStep, layout]

theorem error_step (counter scratch : List Bool) :
    step program (state (some 3) [] counter scratch) = some (state (some 2) [] (false :: counter) scratch) := by
  simp [step, program, state, instructionStep, layout]
  funext port
  cases port with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem halt_step (source counter scratch : List Bool) :
    step program (state (some 2) source counter scratch) = some (state none source counter scratch) := rfl

theorem frame_succ (count : Nat) (payload : List Bool) :
    Encoding.frameCount (count+1) payload = true :: Encoding.frameCount count payload := by
  simp [Encoding.frameCount, List.replicate_succ]

theorem replicate_push (count : Nat) (counter : List Bool) :
    List.replicate count true ++ (true :: counter) = List.replicate (count+1) true ++ counter := by
  rw [List.replicate_succ', List.append_assoc]
  rfl

theorem execution (count : Nat) (payload counter scratch : List Bool) :
    Execution program (state (some 0) (Encoding.frameCount count payload) counter scratch)
      (state none payload (List.replicate count true ++ counter) scratch)
      (2*count+2) (count+1+payload.length+counter.length+scratch.length) := by
  induction count generalizing counter with
  | zero =>
    have done := Execution.refl (program := program) (state none payload counter scratch)
    have trace := Execution.cons (false_step payload counter scratch) (Execution.cons (halt_step payload counter scratch) done)
    have peak : max (live (state (some 0) (false :: payload) counter scratch))
        (max (live (state (some 2) payload counter scratch)) (live (state none payload counter scratch))) =
        1+payload.length+counter.length+scratch.length := by
      simp only [state, live_layout, List.length_cons]
      omega
    rw [peak] at trace
    simpa [Encoding.frameCount] using trace
  | succ count ih =>
    have tail := ih (true :: counter)
    rw [replicate_push] at tail
    have one := Execution.cons (push_step (Encoding.frameCount count payload) counter scratch) tail
    have two := Execution.cons (true_step (Encoding.frameCount count payload) counter scratch) one
    have ticks : (2*count+2)+1+1=2*(count+1)+2 := by omega
    rw [ticks] at two
    have peak : max (live (state (some 0) (true :: Encoding.frameCount count payload) counter scratch))
        (max (live (state (some 1) (Encoding.frameCount count payload) counter scratch))
          (count+1+payload.length+(true :: counter).length+scratch.length)) =
        (count+1)+1+payload.length+counter.length+scratch.length := by
      simp only [state, live_layout, Encoding.frameCount, List.length_append, List.length_replicate, List.length_cons]
      omega
    rw [peak] at two
    simpa only [frame_succ] using two

theorem eof_execution (count : Nat) (counter scratch : List Bool) :
    Execution program (state (some 0) (List.replicate count true) counter scratch)
      (state none [] (false :: (List.replicate count true ++ counter)) scratch)
      (2*count+3) (count+counter.length+scratch.length+1) := by
  induction count generalizing counter with
  | zero =>
    have done := Execution.refl (program := program) (state none [] (false :: counter) scratch)
    have one := Execution.cons (halt_step [] (false :: counter) scratch) done
    have two := Execution.cons (error_step counter scratch) one
    have three := Execution.cons (empty_step counter scratch) two
    have peak : max (live (state (some 0) [] counter scratch))
        (max (live (state (some 3) [] counter scratch))
          (max (live (state (some 2) [] (false :: counter) scratch)) (live (state none [] (false :: counter) scratch)))) =
        counter.length+scratch.length+1 := by
      simp only [state, live_layout, List.length_nil, List.length_cons]
      omega
    rw [peak] at three
    simpa using three
  | succ count ih =>
    have tail := ih (true :: counter)
    rw [replicate_push] at tail
    have one := Execution.cons (push_step (List.replicate count true) counter scratch) tail
    have two := Execution.cons (true_step (List.replicate count true) counter scratch) one
    have ticks : (2*count+3)+1+1=2*(count+1)+3 := by omega
    rw [ticks] at two
    have peak : max (live (state (some 0) (true :: List.replicate count true) counter scratch))
        (max (live (state (some 1) (List.replicate count true) counter scratch))
          (count+(true :: counter).length+scratch.length+1)) = (count+1)+counter.length+scratch.length+1 := by
      simp only [state, live_layout, List.length_cons, List.length_replicate]
      omega
    rw [peak] at two
    simpa only [List.replicate_succ] using two

theorem readCount_sound {input : List Bool} {count payload} (parsed : Encoding.readCount input = some (count,payload)) :
    input = Encoding.frameCount count payload := by
  induction input generalizing count payload with
  | nil => simp [Encoding.readCount] at parsed
  | cons bit input ih =>
    cases bit with
    | false =>
      simp only [Encoding.readCount, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨rfl,rfl⟩ := parsed
      rfl
    | true =>
      cases tail : Encoding.readCount input with
      | none => simp [Encoding.readCount, tail] at parsed
      | some pair =>
        rcases pair with ⟨n,suffix⟩
        simp only [Encoding.readCount, tail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨rfl,rfl⟩ := parsed
        rw [frame_succ, ← ih tail]

theorem readCount_none {input : List Bool} (parsed : Encoding.readCount input = none) :
    input = List.replicate input.length true := by
  induction input with
  | nil => rfl
  | cons bit input ih =>
    cases bit with
    | false => simp [Encoding.readCount] at parsed
    | true =>
      cases tail : Encoding.readCount input with
      | none => simpa only [List.length_cons, List.replicate_succ] using congrArg (true :: ·) (ih tail)
      | some pair => simp [Encoding.readCount, tail] at parsed

theorem initial_state (input : List Bool) : initial program input = state (some 0) input [] [] := by
  unfold initial state
  congr 1
  funext port
  cases port with
  | none => rfl
  | some bit => cases bit <;> rfl

theorem read_success {input : List Bool} {count payload} (parsed : Encoding.readCount input = some (count,payload)) :
    Execution program (initial program input) (state none payload (List.replicate count true) [])
      (2*count+2) input.length := by
  rw [readCount_sound parsed, initial_state]
  simpa [Encoding.frameCount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using execution count payload [] []

theorem read_failure {input : List Bool} (parsed : Encoding.readCount input = none) :
    Execution program (initial program input) (state none [] (false :: List.replicate input.length true) [])
      (2*input.length+3) (input.length+1) := by
  have trace := eof_execution input.length [] []
  have start : state (some 0) (List.replicate input.length true) [] [] = initial program input := by
    rw [← readCount_none parsed]
    exact (initial_state input).symm
  rw [start] at trace
  simpa only [List.append_nil, List.length_nil, Nat.add_zero] using trace

theorem decoder_spec (input : List Bool) :
    match Encoding.readCount input with
    | some (count,payload) => Execution program (initial program input)
        (state none payload (List.replicate count true) []) (2*count+2) input.length
    | none => Execution program (initial program input)
        (state none [] (false :: List.replicate input.length true) []) (2*input.length+3) (input.length+1) := by
  cases parsed : Encoding.readCount input with
  | none => exact read_failure parsed
  | some pair => rcases pair with ⟨count,payload⟩; exact read_success parsed

theorem framed_execution [Fintype K] [DecidableEq K] (ports : Option Bool ↪ Option K)
    (frame : Option K → List Bool) (count : Nat) (payload counter scratch : List Bool) :
    Execution (StackFrames.relocate ports program)
      (StackFrames.embedState ports frame (state (some 0) (Encoding.frameCount count payload) counter scratch))
      (StackFrames.embedState ports frame (state none payload (List.replicate count true ++ counter) scratch))
      (2*count+2) (count+1+payload.length+counter.length+scratch.length+StackFrames.frameBits ports frame) :=
  StackFrames.execution ports frame (execution count payload counter scratch)

def acceptCounter (observed : Option Bool) : Bool := observed != some false

theorem accept_success (count : Nat) : acceptCounter (List.replicate count true).head? = true := by
  cases count <;> simp [acceptCounter, List.replicate_succ]

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 36 := by
  simpa using finiteTM_resident program

end Controller.Complexity.HeaderParser
