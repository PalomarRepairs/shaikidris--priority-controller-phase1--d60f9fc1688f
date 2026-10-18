module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.OperandCheck
public import Controller.Complexity.CountLoop

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A counted operand loop consumes actual saved role bits. Each complete
word is checked or discarded by the finite operand reader. Rejection stops
the loop with its unread source, role tail and count still present. -/
namespace Controller.Complexity.OperandLoop
open StackMachine WordReader
open scoped BigOperators

def fields (frame : Port → List Bool) (roles : List Bool) (count : Nat) : Port → List Bool :=
  Function.update (Function.update (Function.update (Function.update frame (some 18) roles)
    (some 10) (List.replicate count true)) (some 16) []) (some 17) []

def data (frame : Port → List Bool) (roles : List Bool) (count : Nat)
    (status source word : List Bool) : Port → List Bool := bank (fields frame roles count) status source word

theorem data_view (frame : Port → List Bool) (roles : List Bool) (count : Nat)
    (status source word : List Bool) :
    bank (fields frame roles count) status source word=data frame roles count status source word := rfl

theorem data_at (frame : Port → List Bool) (roles : List Bool) (count : Nat)
    (status source word : List Bool) (target : Port) :
    data frame roles count status source word target =
      if target=none then status else if target=some 0 then source else if target=some 1 then word
      else if target=some 2 ∨ target=some 16 ∨ target=some 17 then []
      else if target=some 10 then List.replicate count true else if target=some 18 then roles else frame target := by
  by_cases hc : target=none
  · subst target; simp [data, bank_counter]
  by_cases hs : target=some 0
  · subst target; simp [data, bank_source]
  by_cases hw : target=some 1
  · subst target; simp [data, bank_word]
  by_cases ht : target=some 2
  · subst target; simp [data, bank_scratch]
  have other := bank_other (fields frame roles count) status source word target hc hs hw ht
  simp only [data, other]
  by_cases ha : target=some 16 <;> by_cases hb : target=some 17 <;>
    by_cases hn : target=some 10 <;> by_cases hr : target=some 18 <;> simp_all [fields]

theorem data_decrement (frame : Port → List Bool) (roles : List Bool) (count : Nat) (source : List Bool) :
    Function.update (data frame roles (count+1) [] source []) (some 10) (List.replicate count true)=
      data frame roles count [] source [] := by
  funext target
  by_cases same : target=some 10 <;> simp_all [data_at]

theorem immediate_view (frame : Port → List Bool) (bit : Bool) (roles : List Bool) (count : Nat)
    (source word : List Bool) :
    Function.update (Function.update (data frame (bit :: roles) count [] source word) (some 18) roles) (some 1) []=
      data frame roles count [] source [] := by
  funext target
  by_cases hr : target=some 18 <;> by_cases hw : target=some 1 <;>
    simp_all [data_at]

theorem register_view (frame : Port → List Bool) (bit : Bool) (roles : List Bool) (count : Nat)
    (status source word : List Bool) :
    RegisterRange.bank (Function.update (data frame (bit :: roles) count [] source word) (some 18) roles)
      status [] [] []=data frame roles count status source [] := by
  funext target
  by_cases hs : target=none <;> by_cases hw : target=some 1 <;>
    by_cases ha : target=some 16 <;> by_cases hb : target=some 17 <;>
    by_cases hr : target=some 18 <;> simp_all [RegisterRange.bank_at, data_at]

def accepts (bit : Bool) (word : List Bool) (registers : Nat) : Bool := !bit || decide (Encoding.value word < registers)

theorem body_execution (frame : Port → List Bool) (bit : Bool) (roles : List Bool) (count registers : Nat)
    (word suffix : List Bool) (widthStored : frame (some 8)=List.replicate word.length true)
    (saved : frame (some 9)=List.replicate registers true) :
    ∃ ticks peak, Execution OperandCheck.reader
      ⟨some OperandCheck.reader.main,data frame (bit :: roles) count [] (word++suffix) []⟩
      ⟨none,data frame roles count (if accepts bit word registers then [] else [false]) suffix []⟩ ticks peak ∧
      ticks ≤ word.length*(4*registers+19)+6*registers+26 := by
  have width : fields frame (bit :: roles) count (some 8)=List.replicate word.length true := by simpa [fields] using widthStored
  cases bit with
  | false =>
    obtain ⟨peak,trace⟩ := OperandCheck.read_immediate (fields frame (false :: roles) count) word suffix roles width (by simp [fields])
    refine ⟨15*word.length+15,peak,?_,?_⟩
    · simpa only [data_view, immediate_view, accepts, Bool.not_false, Bool.true_or, Bool.true_eq, ite_true] using trace
    · have positive : 0 ≤ word.length*(4*registers+4) := Nat.zero_le _
      have identity : word.length*(4*registers+19)=15*word.length+word.length*(4*registers+4) := by ring
      omega
  | true =>
    obtain ⟨ticks,peak,trace,bound⟩ := OperandCheck.read_register (fields frame (true :: roles) count) word suffix roles registers width
      (by simp [fields]) (by simp [fields]) (by simp [fields]) (by simpa [fields] using saved)
    refine ⟨ticks,peak,?_,bound⟩
    simpa only [data_view, register_view, accepts, Bool.not_true, Bool.false_or, decide_eq_true_eq] using trace

def program := CountLoop.program OperandCheck.reader (some 10) none Option.isNone

inductive Result where
  | done (source : List Bool)
  | invalid (roles source : List Bool)
  | short (roles : List Bool) (missing : Nat) (fragment : List Bool)
  deriving DecidableEq

def scan (width registers : Nat) : List Bool → List Bool → Result
  | [],source => .done source
  | bit :: roles,source => if width ≤ source.length then
      if accepts bit (source.take width) registers then scan width registers roles (source.drop width)
      else .invalid roles (source.drop width)
    else .short (bit :: roles) (width-source.length-1) source

def endpoint (frame : Port → List Bool) : Result → Port → List Bool
  | .done source => data frame [] 0 [] source []
  | .invalid roles source => data frame roles roles.length [false] source []
  | .short roles missing fragment => data frame roles (roles.length-1) (false :: List.replicate missing true) [] fragment.reverse

theorem body_short (frame : Port → List Bool) (roles : List Bool) (count missing : Nat) (source : List Bool)
    (stored : frame (some 8)=List.replicate (source.length+missing+1) true) :
    Execution OperandCheck.reader
      ⟨some OperandCheck.reader.main,data frame roles count [] source []⟩
      ⟨none,data frame roles count (false :: List.replicate missing true) [] source.reverse⟩
      (5*(source.length+missing+1)+3*source.length+10)
      ((source.length+missing+1)+source.length+ambientBits (fields frame roles count)) := by
  exact OperandCheck.read_short (fields frame roles count) missing source (by simpa [fields] using stored)

theorem total_execution (frame : Port → List Bool) (width registers : Nat) (roles source : List Bool)
    (stored : frame (some 8)=List.replicate width true) (saved : frame (some 9)=List.replicate registers true) :
    ∃ ticks peak, Execution program ⟨some program.main,data frame roles roles.length [] source []⟩
      ⟨none,endpoint frame (scan width registers roles source)⟩ ticks peak ∧
      ticks ≤ roles.length*(width*(4*registers+19)+6*registers+27)+2 := by
  induction roles generalizing source with
  | nil =>
    have trace := CountLoop.empty OperandCheck.reader (some 10) none Option.isNone (data frame [] 0 [] source []) (by simp [data_at])
    exact ⟨2,_,trace,by simp⟩
  | cons bit roles ih =>
    have counted : data frame (bit :: roles) (roles.length+1) [] source [] (some 10)=
        true :: List.replicate roles.length true := by simp [data_at, List.replicate_succ]
    by_cases enough : width ≤ source.length
    · let word := source.take width
      let suffix := source.drop width
      have wordWidth : word.length=width := by simp only [word, List.length_take, Nat.min_eq_left enough]
      obtain ⟨bodyTicks,bodyPeak,bodyRun,bodyBound⟩ := body_execution frame bit roles roles.length registers word suffix
        (by simpa only [wordWidth] using stored) saved
      have joined : word++suffix=source := List.take_append_drop width source
      have adjusted : Execution OperandCheck.reader
          ⟨some OperandCheck.reader.main,Function.update (data frame (bit :: roles) (roles.length+1) [] source [])
            (some 10) (List.replicate roles.length true)⟩
          ⟨none,data frame roles roles.length (if accepts bit word registers then [] else [false]) suffix []⟩ bodyTicks bodyPeak := by
        simpa only [data_decrement, joined] using bodyRun
      simp only [wordWidth] at bodyBound
      by_cases accepted : accepts bit word registers=true
      · rw [accepted, ite_eq_left (show (true : Bool)=true from rfl)] at adjusted
        obtain ⟨tailTicks,tailPeak,tailRun,tailBound⟩ := ih suffix
        obtain ⟨peak,trace⟩ := CountLoop.next (some 10) none Option.isNone counted adjusted (by simp [data_at]) tailRun
        refine ⟨bodyTicks+tailTicks+1,peak,?_,?_⟩
        · simpa only [program, scan, ite_eq_left enough, word, suffix, accepted, Bool.true_eq, ite_true, List.length_cons] using trace
        · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega
      · have rejected : accepts bit word registers=false := Bool.eq_false_iff.mpr accepted
        rw [rejected, ite_eq_right (by decide : ¬(false : Bool)=true)] at adjusted
        obtain ⟨peak,trace⟩ := CountLoop.reject (some 10) none Option.isNone counted adjusted (by simp [data_at])
        refine ⟨bodyTicks+2,peak,?_,?_⟩
        · simpa only [program, scan, ite_eq_left enough, word, suffix, rejected, ite_eq_right (by decide : ¬(false : Bool)=true), endpoint, List.length_cons] using trace
        · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega
    · let missing := width-source.length-1
      have full : width=source.length+missing+1 := by dsimp [missing]; omega
      have bodyRun := body_short frame (bit :: roles) roles.length missing source (by simpa only [← full] using stored)
      have adjusted : Execution OperandCheck.reader
          ⟨some OperandCheck.reader.main,Function.update (data frame (bit :: roles) (roles.length+1) [] source [])
            (some 10) (List.replicate roles.length true)⟩
          ⟨none,data frame (bit :: roles) roles.length (false :: List.replicate missing true) [] source.reverse⟩
          (5*width+3*source.length+10) (width+source.length+ambientBits (fields frame (bit :: roles) roles.length)) := by
        simpa only [data_decrement, full] using bodyRun
      obtain ⟨peak,trace⟩ := CountLoop.reject (some 10) none Option.isNone counted adjusted (by simp [data_at])
      refine ⟨(5*width+3*source.length+10)+2,peak,?_,?_⟩
      · simpa only [program, scan, ite_eq_right enough, endpoint, List.length_cons, Nat.add_sub_cancel, missing] using trace
      · have positive := Nat.zero_le (width*(4*registers+11))
        have identity : width*(4*registers+19)=8*width+width*(4*registers+11) := by ring
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega

end Controller.Complexity.OperandLoop
