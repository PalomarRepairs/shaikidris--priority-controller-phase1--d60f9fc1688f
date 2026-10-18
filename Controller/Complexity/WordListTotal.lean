module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordListReader

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Total execution of the fixed word-list parser, including incomplete
headers and words. A finite reference result records retained fragment data;
the execution theorem links it to the actual parser and bounds every run. -/
namespace Controller.Complexity.WordListTotal
open StackMachine StackBlocks WordReader WordListReader

inductive ScanResult where
  | done (suffix buffer : List Bool)
  | short (remaining missing : Nat) (fragment buffer : List Bool)
  deriving DecidableEq

def scan (width : Nat) : Nat → List Bool → List Bool → ScanResult
  | 0,source,buffer => .done source buffer
  | count+1,source,buffer => if width ≤ source.length then
      scan width count (source.drop width) ((source.take width).reverse++buffer)
    else .short count (width-source.length-1) source buffer

def beforeRestore (frame : Port → List Bool) : ScanResult → Port → List Bool
  | .done suffix buffer => data frame 0 suffix buffer
  | .short remaining missing fragment buffer =>
      bank (fields frame remaining buffer) (false :: List.replicate missing true) [] fragment.reverse

def afterRestore (frame : Port → List Bool) : ScanResult → Port → List Bool
  | .done suffix buffer => data frame 0 suffix buffer.reverse
  | .short remaining missing fragment buffer => beforeRestore frame (.short remaining missing fragment buffer)

theorem body_short (frame : Port → List Bool) (count missing : Nat) (source buffer : List Bool)
    (stored : frame (some 8) = List.replicate (source.length+missing+1) true) :
    ∃ peak, Execution body ⟨some body.main,data frame count source buffer⟩
      ⟨none,beforeRestore frame (.short count missing source buffer)⟩
      (5*(source.length+missing+1)+3*source.length+10) peak := by
  have widthStored : fields frame count buffer (some 8)=List.replicate (source.length+missing+1) true := by
    simpa [fields] using stored
  have reading := WidthReader.short_execution (fields frame count buffer) missing source widthStored
  have rejected : Option.isNone ((bank (fields frame count buffer) (false :: List.replicate missing true) [] source.reverse none).head?) = false := by
    simp [bank_counter]
  have trace := GuardedLink.failure moveWord none Option.isNone reading rejected
  have ticks : (5*(source.length+missing+1)+3*source.length+9)+1=5*(source.length+missing+1)+3*source.length+10 := by omega
  exact ⟨_,by simpa only [body, data, beforeRestore, ticks] using trace⟩

theorem loop_total (frame : Port → List Bool) (width count : Nat) (source buffer : List Bool)
    (stored : frame (some 8) = List.replicate width true) :
    ∃ ticks peak, Execution loop ⟨some loop.main,data frame count source buffer⟩
      ⟨none,beforeRestore frame (scan width count source buffer)⟩ ticks peak ∧ ticks ≤ count*(16*width+15)+2 := by
  induction count generalizing source buffer with
  | zero =>
    have trace := CountLoop.empty body (some 10) none Option.isNone (data frame 0 source buffer) (by simp [data_count])
    exact ⟨2,_,by simpa only [loop, scan, beforeRestore] using trace,by simp⟩
  | succ count ih =>
    have counted : data frame (count+1) source buffer (some 10) = true :: List.replicate count true := by
      simp [data_count, List.replicate_succ]
    by_cases enough : width ≤ source.length
    · let word := source.take width
      let rest := source.drop width
      have wordWidth : word.length=width := by simp only [word, List.length_take, Nat.min_eq_left enough]
      obtain ⟨tailTicks,tailPeak,tailRun,tailBound⟩ := ih rest (word.reverse++buffer)
      obtain ⟨bodyPeak,bodyRun⟩ := body_execution frame count word rest buffer (by simpa only [wordWidth] using stored)
      have joined : word++rest=source := List.take_append_drop width source
      have adjusted : Execution body
          ⟨some body.main,Function.update (data frame (count+1) source buffer) (some 10) (List.replicate count true)⟩
          ⟨none,data frame count rest (word.reverse++buffer)⟩ (16*width+14) bodyPeak := by
        simpa only [data_decrement, joined, wordWidth] using bodyRun
      have accepted : Option.isNone ((data frame count rest (word.reverse++buffer) none).head?) = true := by simp [data_guard]
      obtain ⟨peak,trace⟩ := CountLoop.next (some 10) none Option.isNone counted adjusted accepted tailRun
      refine ⟨(16*width+14)+tailTicks+1,peak,?_,?_⟩
      · simpa only [loop, scan, ite_eq_left enough, word, rest] using trace
      · simp only [Nat.add_mul, Nat.one_mul]
        omega
    · let missing := width-source.length-1
      have full : width=source.length+missing+1 := by dsimp [missing]; omega
      obtain ⟨bodyPeak,bodyRun⟩ := body_short frame count missing source buffer (by simpa only [← full] using stored)
      have adjusted : Execution body
          ⟨some body.main,Function.update (data frame (count+1) source buffer) (some 10) (List.replicate count true)⟩
          ⟨none,beforeRestore frame (.short count missing source buffer)⟩ (5*width+3*source.length+10) bodyPeak := by
        simpa only [data_decrement, full] using bodyRun
      have rejected : Option.isNone ((beforeRestore frame (.short count missing source buffer) none).head?) = false := by
        simp [beforeRestore, bank_counter]
      obtain ⟨peak,trace⟩ := CountLoop.reject (some 10) none Option.isNone counted adjusted rejected
      refine ⟨(5*width+3*source.length+10)+2,peak,?_,?_⟩
      · simpa only [loop, scan, ite_eq_right enough, missing] using trace
      · simp only [Nat.add_mul, Nat.one_mul]
        omega

theorem scan_mass (width count : Nat) (source buffer : List Bool) :
    match scan width count source buffer with
    | .done suffix output => suffix.length+output.length=source.length+buffer.length
    | .short _ _ fragment output => fragment.length+output.length=source.length+buffer.length := by
  induction count generalizing source buffer with
  | zero => rfl
  | succ count ih =>
    by_cases enough : width ≤ source.length
    · have bound := ih (source.drop width) ((source.take width).reverse++buffer)
      simp only [List.length_drop, List.length_append, List.length_reverse, List.length_take,
        Nat.min_eq_left enough] at bound
      have mass : (source.length-width)+(width+buffer.length)=source.length+buffer.length := by omega
      rw [mass] at bound
      simpa only [scan, ite_eq_left enough] using bound
    · simp only [scan, ite_eq_right enough]

theorem payload_total (frame : Port → List Bool) (width count : Nat) (source : List Bool)
    (stored : frame (some 8) = List.replicate width true) :
    ∃ ticks peak, Execution restorePayload ⟨some restorePayload.main,data frame count source []⟩
      ⟨none,afterRestore frame (scan width count source [])⟩ ticks peak ∧
      ticks ≤ count*(16*width+15)+6*source.length+8 := by
  obtain ⟨ticks,peak,trace,bound⟩ := loop_total frame width count source [] stored
  cases result : scan width count source [] with
  | done suffix buffer =>
    rw [result] at trace
    obtain ⟨restorePeak,restoring⟩ := restore_execution frame suffix buffer
    have accepted : Option.isNone ((data frame 0 suffix buffer none).head?) = true := by simp [data_guard]
    have run := GuardedLink.success none Option.isNone trace restoring accepted
    have mass := scan_mass width count source []
    rw [result] at mass
    simp only [List.length_nil, Nat.add_zero] at mass
    exact ⟨_,_,by simpa only [restorePayload, beforeRestore, afterRestore, result] using run,by omega⟩
  | short remaining missing fragment buffer =>
    rw [result] at trace
    have rejected : Option.isNone ((beforeRestore frame (.short remaining missing fragment buffer) none).head?) = false := by
      simp [beforeRestore, bank_counter]
    have run := GuardedLink.failure restoreMachine none Option.isNone trace rejected
    exact ⟨_,_,by simpa only [restorePayload, afterRestore, result] using run,by omega⟩

def parseResult (frame : Port → List Bool) (width : Nat) (input : List Bool) : Port → List Bool :=
  match Encoding.readCount input with
  | none => bank frame (false :: List.replicate input.length true) [] []
  | some (count,payload) => afterRestore (Function.update frame (some 12) (List.replicate count true))
      (scan width count payload [])

theorem total_time (frame : Port → List Bool) (width : Nat) (input : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) :
    ∃ ticks peak, Execution WordListReader.program ⟨some WordListReader.program.main,bank frame [] input []⟩
      ⟨none,parseResult frame width input⟩ ticks peak ∧ ticks ≤ input.length*(16*width+30)+16 := by
  cases parsed : Encoding.readCount input with
  | none =>
    have shape := HeaderParser.readCount_none parsed
    have header := ColdInput.read_save_eof frame 10 input.length []
    have rejected : Option.isNone ((bank frame (false :: List.replicate input.length true) [] [] none).head?) = false := by
      simp [bank_counter]
    have trace := GuardedLink.failure payloadProgram none Option.isNone header rejected
    have entry := congrArg (fun source => (⟨some WordListReader.program.main,bank frame [] source []⟩ : State (Fin 31) _)) shape
    change Execution WordListReader.program
      ⟨some WordListReader.program.main,bank frame [] (List.replicate input.length true) []⟩ _ _ _ at trace
    rw [← entry] at trace
    have growth : 2 ≤ 16*width+30 := by omega
    have bound := Nat.mul_le_mul_left input.length growth
    exact ⟨_,_,by simpa only [parseResult, parsed] using trace,by omega⟩
  | some pair =>
    rcases pair with ⟨count,payload⟩
    have shape := HeaderParser.readCount_sound parsed
    let savedFrame := Function.update frame (some 12) (List.replicate count true)
    have savedWidth : savedFrame (some 8)=List.replicate width true := by simpa [savedFrame] using stored
    obtain ⟨copyPeak,copyRun⟩ := count_copy_execution frame count payload savedEmpty
    obtain ⟨payloadTicks,payloadPeak,payloadRun,payloadBound⟩ := payload_total savedFrame width count payload savedWidth
    have bodyRun := copyRun.link payloadRun
    have header := ColdInput.read_save_execution frame 10 (by decide) (by decide) (by decide) count payload [] countEmpty
    rw [← empty_buffer frame count payload bufferEmpty] at header
    have accepted : Option.isNone ((data frame count payload [] none).head?) = true := by simp [data_guard]
    have trace := GuardedLink.success none Option.isNone header bodyRun accepted
    change Execution WordListReader.program
      ⟨some WordListReader.program.main,bank frame [] (Encoding.frameCount count payload) []⟩ _ _ _ at trace
    have entry := congrArg (fun source => (⟨some WordListReader.program.main,bank frame [] source []⟩ : State (Fin 31) _)) shape
    rw [← entry] at trace
    have length : input.length=count+payload.length+1 := by
      rw [shape]
      simp only [Encoding.frameCount, List.length_append, List.length_replicate, List.length_cons]
      omega
    have counts : count ≤ input.length := by omega
    have payloadSize : payload.length ≤ input.length := by omega
    have product := Nat.mul_le_mul_right (16*width+24) counts
    have suffixBound := Nat.mul_le_mul_left 6 payloadSize
    have localIdentity : (4*count+4)+(5*count+4+(count*(16*width+15)+6*payload.length+8)) =
        count*(16*width+24)+6*payload.length+16 := by ring
    have globalIdentity : input.length*(16*width+24)+6*input.length+16 = input.length*(16*width+30)+16 := by ring
    have tickBound : (4*count+4)+(5*count+4+payloadTicks) ≤ input.length*(16*width+30)+16 := by
      calc
        _ ≤ (4*count+4)+(5*count+4+(count*(16*width+15)+6*payload.length+8)) := by omega
        _ = count*(16*width+24)+6*payload.length+16 := localIdentity
        _ ≤ input.length*(16*width+24)+6*input.length+16 := by omega
        _ = _ := globalIdentity
    exact ⟨_,_,by simpa only [parseResult, parsed, savedFrame, payloadProgram] using trace,tickBound⟩

theorem total_resources (frame : Port → List Bool) (width : Nat) (input : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) :
    ∃ ticks peak, Execution WordListReader.program ⟨some WordListReader.program.main,bank frame [] input []⟩
      ⟨none,parseResult frame width input⟩ ticks peak ∧ ticks ≤ input.length*(16*width+30)+16 ∧
      peak ≤ input.length+ambientBits frame+(input.length*(16*width+30)+16) := by
  obtain ⟨ticks,peak,trace,bound⟩ := total_time frame width input stored countEmpty bufferEmpty savedEmpty
  have space := trace.peak_le
  simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
  exact ⟨ticks,peak,trace,bound,by omega⟩

def ScanResult.success : ScanResult → Bool
  | .done .. => true
  | .short .. => false

theorem scan_success (width count : Nat) (source buffer : List Bool) :
    (scan width count source buffer).success ↔ count*width ≤ source.length := by
  induction count generalizing source buffer with
  | zero => simp [scan, ScanResult.success]
  | succ count ih =>
    by_cases enough : width ≤ source.length
    · simp only [scan, ite_eq_left enough, ih, List.length_drop, Nat.add_mul, Nat.one_mul]
      omega
    · simp only [scan, ite_eq_right enough, ScanResult.success, Bool.false_eq_true, false_iff, Nat.add_mul, Nat.one_mul]
      omega

theorem readWords_success (width count : Nat) (source : List Bool) :
    (Encoding.readWords width count source).isSome ↔ count*width ≤ source.length := by
  induction count generalizing source with
  | zero => simp [Encoding.readWords]
  | succ count ih =>
    by_cases enough : width ≤ source.length
    · have prefixLength : (source.take width).length=width := by simp only [List.length_take, Nat.min_eq_left enough]
      have same : (Encoding.readWords width (count+1) source).isSome =
          (Encoding.readWords width count (source.drop width)).isSome := by
        simp only [Encoding.readWords, Encoding.decodeWord, prefixLength, Bind.bind, Option.bind]
        cases Encoding.readWords width count (source.drop width) <;> rfl
      rw [same, ih]
      simp only [List.length_drop, Nat.add_mul, Nat.one_mul]
      omega
    · have prefixLength : (source.take width).length≠width := by simp only [List.length_take]; omega
      have rejected := Encoding.decodeWord_wrong_length (source.take width) prefixLength
      simp only [Encoding.readWords, rejected, Bind.bind, Option.bind, Option.isSome_none,
        Bool.false_eq_true, false_iff, Nat.add_mul, Nat.one_mul]
      omega

theorem parse_accept (frame : Port → List Bool) (width : Nat) (input : List Bool) :
    ((parseResult frame width input none).head?).isNone ↔ (Encoding.readFramedWords width input).isSome := by
  cases parsed : Encoding.readCount input with
  | none => simp [parseResult, parsed, bank_counter, Encoding.readFramedWords]
  | some pair =>
    rcases pair with ⟨count,payload⟩
    have equivalence := (scan_success width count payload []).trans (readWords_success width count payload).symm
    cases result : scan width count payload [] with
    | done suffix buffer =>
      rw [result] at equivalence
      simpa [parseResult, parsed, afterRestore, result, data_guard, ScanResult.success, Encoding.readFramedWords] using equivalence
    | short remaining missing fragment buffer =>
      rw [result] at equivalence
      simpa [parseResult, parsed, afterRestore, beforeRestore, result, bank_counter, ScanResult.success, Encoding.readFramedWords] using equivalence

theorem stored_width_le_ambient (frame : Port → List Bool) (width : Nat)
    (stored : frame (some 8)=List.replicate width true) : width ≤ ambientBits frame := by
  have bound := Finset.single_le_sum (f := fun target : Port => (bank frame [] [] [] target).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have cell := bank_other frame [] [] [] (some 8) (by decide) (by decide) (by decide) (by decide)
  rw [cell, stored, List.length_replicate] at bound
  have total := bank_live frame (none : Option Unit) [] [] []
  simp only [List.length_nil, Nat.zero_add, Nat.add_zero, live] at total
  exact bound.trans_eq total

theorem total_polynomial (frame : Port → List Bool) (width : Nat) (input : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) :
    ∃ ticks peak, Execution WordListReader.program ⟨some WordListReader.program.main,bank frame [] input []⟩
      ⟨none,parseResult frame width input⟩ ticks peak ∧
      ticks ≤ 16*(input.length+ambientBits frame)^2+30*(input.length+ambientBits frame)+16 ∧
      peak ≤ 16*(input.length+ambientBits frame)^2+31*(input.length+ambientBits frame)+16 := by
  obtain ⟨ticks,peak,trace,timeBound,spaceBound⟩ := total_resources frame width input stored countEmpty bufferEmpty savedEmpty
  have widthBound : width ≤ input.length+ambientBits frame := by
    have storedSize := stored_width_le_ambient frame width stored
    omega
  have inputBound : input.length ≤ input.length+ambientBits frame := by omega
  have product := Nat.mul_le_mul inputBound (Nat.add_le_add_right (Nat.mul_le_mul_left 16 widthBound) 30)
  have identity : (input.length+ambientBits frame)*(16*(input.length+ambientBits frame)+30)+16 =
      16*(input.length+ambientBits frame)^2+30*(input.length+ambientBits frame)+16 := by ring
  have finalTime : ticks ≤ 16*(input.length+ambientBits frame)^2+30*(input.length+ambientBits frame)+16 := by
    rw [← identity]
    omega
  have space := trace.peak_le
  simp only [bank_live, List.length_nil, Nat.zero_add, Nat.add_zero] at space
  exact ⟨ticks,peak,trace,finalTime,by omega⟩

end Controller.Complexity.WordListTotal
