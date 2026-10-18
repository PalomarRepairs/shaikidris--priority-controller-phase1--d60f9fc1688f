module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WidthReader
public import Controller.Complexity.CountLoop

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A fixed finite parser consumes a count-framed list of binary words. A
persistent width supplies each charged read. Complete words accumulate in
reverse order; a guarded reversal restores the encoded list payload. -/
namespace Controller.Complexity.WordListReader
open StackMachine StackBlocks WordReader
open scoped BigOperators

def fields (frame : Port → List Bool) (count : Nat) (buffer : List Bool) : Port → List Bool :=
  Function.update (Function.update frame (some 10) (List.replicate count true)) (some 11) buffer

def data (frame : Port → List Bool) (count : Nat) (source buffer : List Bool) : Port → List Bool :=
  bank (fields frame count buffer) [] source []

theorem data_at (frame : Port → List Bool) (count : Nat) (source buffer : List Bool) (target : Port) :
    data frame count source buffer target =
      if target=none then [] else if target=some 0 then source else if target=some 1 then []
      else if target=some 2 then [] else if target=some 10 then List.replicate count true
      else if target=some 11 then buffer else frame target := by
  by_cases hc : target=none <;> by_cases hs : target=some 0 <;>
    by_cases hw : target=some 1 <;> by_cases ht : target=some 2 <;>
    by_cases hn : target=some 10 <;> by_cases hb : target=some 11 <;>
    simp_all [data, fields, bank, cursorFrame, cursorPorts_apply, StackFrames.embedStorage, layout]

theorem data_count (frame : Port → List Bool) (count : Nat) (source buffer : List Bool) :
    data frame count source buffer (some 10) = List.replicate count true := by simp [data_at]

theorem data_guard (frame : Port → List Bool) (count : Nat) (source buffer : List Bool) :
    data frame count source buffer none = [] := by simp [data_at]

theorem data_decrement (frame : Port → List Bool) (count : Nat) (source buffer : List Bool) :
    Function.update (data frame (count+1) source buffer) (some 10) (List.replicate count true) =
      data frame count source buffer := by
  funext target
  by_cases same : target=some 10 <;> simp_all [data_at]

theorem transfer_storage (frame : Port → List Bool) (count : Nat) (source word buffer : List Bool) :
    storage (data frame count source []) (some 1) (some 11) word buffer =
      bank (fields frame count buffer) [] source word := by
  funext target
  by_cases hc : target=none <;> by_cases hs : target=some 0 <;>
    by_cases hw : target=some 1 <;> by_cases ht : target=some 2 <;>
    by_cases hn : target=some 10 <;> by_cases hb : target=some 11 <;>
    simp_all [storage, data, fields, bank, cursorFrame, cursorPorts_apply, StackFrames.embedStorage, layout]

def moveWord := transfer (K := Fin 31) (some 1) (some 11)
theorem moveWord_main : moveWord.main = 0 := rfl
def body := GuardedLink.program WidthReader.program moveWord none Option.isNone
def loop := CountLoop.program body (some 10) none Option.isNone

theorem move_word_execution (frame : Port → List Bool) (count : Nat) (source word buffer : List Bool) :
    ∃ peak, Execution moveWord ⟨some moveWord.main,bank (fields frame count buffer) [] source word⟩
      ⟨none,data frame count source (word.reverse++buffer)⟩ (2*word.length+2) peak := by
  rw [moveWord_main]
  unfold data
  have trace := transfer_execution (data frame count source []) (source := some 1) (destination := some 11)
    (by decide) word buffer
  simpa only [moveWord, state, transfer_storage] using Exists.intro _ trace

theorem body_execution (frame : Port → List Bool) (count : Nat) (word suffix buffer : List Bool)
    (stored : frame (some 8) = List.replicate word.length true) :
    ∃ peak, Execution body ⟨some body.main,data frame count (word++suffix) buffer⟩
      ⟨none,data frame count suffix (word.reverse++buffer)⟩ (16*word.length+14) peak := by
  have widthStored : fields frame count buffer (some 8) = List.replicate word.length true := by simpa [fields] using stored
  have reading := WidthReader.execution (fields frame count buffer) word suffix widthStored
  obtain ⟨movePeak,moving⟩ := move_word_execution frame count suffix word buffer
  have accepted : Option.isNone ((bank (fields frame count buffer) [] suffix word none).head?) = true := by simp [bank_counter]
  have trace := GuardedLink.success none Option.isNone reading moving accepted
  have ticks : (14*word.length+12)+(2*word.length+2)=16*word.length+14 := by omega
  exact ⟨_,by simpa only [body, data, ticks] using trace⟩

theorem loop_execution (frame : Port → List Bool) (width : Nat) (words : List (List Bool)) (suffix buffer : List Bool)
    (stored : frame (some 8) = List.replicate width true) (widths : ∀ word ∈ words, word.length=width) :
    ∃ peak, Execution loop ⟨some loop.main,data frame words.length (words.flatten++suffix) buffer⟩
      ⟨none,data frame 0 suffix (words.flatten.reverse++buffer)⟩ (words.length*(16*width+15)+2) peak := by
  induction words generalizing buffer with
  | nil =>
    have trace := CountLoop.empty body (some 10) none Option.isNone (data frame 0 suffix buffer) (by simp [data_count])
    exact ⟨_,by simpa only [loop, List.length_nil, List.flatten_nil, List.nil_append, List.reverse_nil, Nat.zero_mul, Nat.zero_add] using trace⟩
  | cons word words ih =>
    have wordWidth := widths word (by simp)
    obtain ⟨tailPeak,tailRun⟩ := ih (word.reverse++buffer) (by intro item member; exact widths item (by simp [member]))
    obtain ⟨bodyPeak,bodyRun⟩ := body_execution frame words.length word (words.flatten++suffix) buffer (by simpa only [wordWidth] using stored)
    have counted : data frame (words.length+1) (word++(words.flatten++suffix)) buffer (some 10) =
        true :: List.replicate words.length true := by simp [data_count, List.replicate_succ]
    have adjusted : Execution body
        ⟨some body.main,Function.update (data frame (words.length+1) (word++(words.flatten++suffix)) buffer)
          (some 10) (List.replicate words.length true)⟩
        ⟨none,data frame words.length (words.flatten++suffix) (word.reverse++buffer)⟩ (16*width+14) bodyPeak := by
      simpa only [data_decrement, wordWidth] using bodyRun
    have accepted : Option.isNone ((data frame words.length (words.flatten++suffix) (word.reverse++buffer) none).head?) = true := by
      simp [data_guard]
    obtain ⟨peak,trace⟩ := CountLoop.next (some 10) none Option.isNone counted adjusted accepted tailRun
    have ticks : (16*width+14)+(words.length*(16*width+15)+2)+1 = (word :: words).length*(16*width+15)+2 := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    exact ⟨peak,by simpa only [loop, List.length_cons, List.flatten_cons, List.append_assoc,
      List.reverse_append, ticks] using trace⟩

def reversePorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 11) none (some 2) (by decide) (by decide) (by decide)

theorem reversePorts_apply (port : Option Bool) : reversePorts port =
    (match port with | none => some 11 | some false => none | some true => some 2) := rfl

theorem reverse_storage (frame : Port → List Bool) (source buffer : List Bool) :
    StackFrames.embedStorage reversePorts (data frame 0 source []) (layout buffer [] []) = data frame 0 source buffer := by
  funext target
  by_cases hc : target=none <;> by_cases hs : target=some 0 <;>
    by_cases hw : target=some 1 <;> by_cases ht : target=some 2 <;>
    by_cases hn : target=some 10 <;> by_cases hb : target=some 11 <;>
    simp_all [StackFrames.embedStorage, reversePorts_apply, layout, data_at]

def restoreMachine := StackFrames.relocate reversePorts reverseProgram
def restorePayload := GuardedLink.program loop restoreMachine none Option.isNone


theorem restore_execution (frame : Port → List Bool) (source buffer : List Bool) :
    ∃ peak, Execution restoreMachine ⟨some restoreMachine.main,data frame 0 source buffer⟩
      ⟨none,data frame 0 source buffer.reverse⟩ (6*buffer.length+6) peak := by
  have trace := StackFrames.reversal reversePorts (data frame 0 source []) buffer
  exact ⟨_,by simpa only [restoreMachine, StackFrames.relocate, StackFrames.embedState, initial_layout,
    terminal_layout, reverse_storage] using trace⟩

theorem empty_buffer (frame : Port → List Bool) (count : Nat) (source : List Bool) (empty : frame (some 11)=[]) :
    data frame count source [] = bank (Function.update frame (some 10) (List.replicate count true)) [] source [] := by
  unfold data fields
  rw [ColdInput.update_empty _ (some 11) (by simpa using empty)]

def countPorts : Option Bool ↪ Port :=
  StackFrames.threePorts (some 10) (some 12) (some 2) (by decide) (by decide) (by decide)

theorem countPorts_apply (port : Option Bool) : countPorts port =
    (match port with | none => some 10 | some false => some 12 | some true => some 2) := rfl

theorem copy_count_start (frame : Port → List Bool) (count : Nat) (source : List Bool) (empty : frame (some 12)=[]) :
    StackFrames.embedStorage countPorts (data frame count source []) (layout (List.replicate count true) [] []) =
      data frame count source [] := by
  funext target
  by_cases hc : target=some 10 <;> by_cases hd : target=some 12 <;> by_cases hs : target=some 2 <;>
    simp_all [StackFrames.embedStorage, countPorts_apply, layout, data_at]

theorem copy_count_finish (frame : Port → List Bool) (count : Nat) (source : List Bool) :
    StackFrames.embedStorage countPorts (data frame count source [])
      (layout (List.replicate count true) (List.replicate count true) []) =
      data (Function.update frame (some 12) (List.replicate count true)) count source [] := by
  funext target
  by_cases hc : target=none <;> by_cases hs : target=some 0 <;>
    by_cases hw : target=some 1 <;> by_cases ht : target=some 2 <;>
    by_cases hn : target=some 10 <;> by_cases hb : target=some 11 <;> by_cases hd : target=some 12 <;>
    simp_all [StackFrames.embedStorage, countPorts_apply, layout, data_at]

def countMachine := StackFrames.relocate countPorts StackCopy.program
def payloadProgram := link countMachine restorePayload
def program := GuardedLink.program (ColdInput.readSave 10) payloadProgram none Option.isNone

theorem count_copy_execution (frame : Port → List Bool) (count : Nat) (source : List Bool) (empty : frame (some 12)=[]) :
    ∃ peak, Execution countMachine ⟨some countMachine.main,data frame count source []⟩
      ⟨none,data (Function.update frame (some 12) (List.replicate count true)) count source []⟩ (5*count+4) peak := by
  have trace := StackCopy.framed_execution countPorts (data frame count source []) (List.replicate count true) []
  exact ⟨_,by simpa only [countMachine, StackFrames.relocate, StackFrames.embedState, List.append_nil,
    copy_count_start frame count source empty, copy_count_finish, List.length_replicate] using trace⟩

theorem encoded_payload (frame : Port → List Bool) (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) :
    ∃ peak, Execution restorePayload ⟨some restorePayload.main,data frame words.length (Encoding.wordList width words++suffix) []⟩
      ⟨none,data frame 0 suffix (Encoding.wordList width words)⟩ (words.length*(22*width+15)+8) peak := by
  let chunks := words.map (Encoding.wordEncoding width).encode
  have concatenation : chunks.flatten=Encoding.wordList width words := rfl
  have chunkCount : chunks.length=words.length := List.length_map ..
  have widths : ∀ item ∈ chunks, item.length=width := by
    intro item member
    obtain ⟨word,_,rfl⟩ := List.mem_map.mp member
    exact Encoding.word_length word
  obtain ⟨loopPeak,loopRun⟩ := loop_execution frame width chunks suffix [] stored widths
  simp only [chunkCount, concatenation, List.append_nil] at loopRun
  obtain ⟨restorePeak,restoreRun⟩ := restore_execution frame suffix (Encoding.wordList width words).reverse
  simp only [List.reverse_reverse, List.length_reverse, Encoding.wordList_length] at restoreRun
  have accepted : Option.isNone ((data frame 0 suffix (Encoding.wordList width words).reverse none).head?) = true := by simp [data_guard]
  have trace := GuardedLink.success none Option.isNone loopRun restoreRun accepted
  have ticks : (words.length*(16*width+15)+2)+(6*(width*words.length)+6)=words.length*(22*width+15)+8 := by ring
  exact ⟨_,by simpa only [restorePayload, ticks] using trace⟩

theorem execution (frame : Port → List Bool) (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) :
    ∃ peak, Execution program ⟨some program.main,bank frame [] (Encoding.encodeWords width words++suffix) []⟩
      ⟨none,data (Function.update frame (some 12) (List.replicate words.length true)) 0 suffix (Encoding.wordList width words)⟩
      (words.length*(22*width+24)+16) peak := by
  let savedFrame := Function.update frame (some 12) (List.replicate words.length true)
  have savedWidth : savedFrame (some 8)=List.replicate width true := by simpa [savedFrame] using stored
  obtain ⟨copyPeak,copyRun⟩ := count_copy_execution frame words.length (Encoding.wordList width words++suffix) savedEmpty
  obtain ⟨payloadPeak,payloadRun⟩ := encoded_payload savedFrame words suffix savedWidth
  have payload := copyRun.link payloadRun
  have header := ColdInput.read_save_execution frame 10 (by decide) (by decide) (by decide) words.length
    (Encoding.wordList width words++suffix) [] countEmpty
  rw [← empty_buffer frame words.length _ bufferEmpty] at header
  have accepted : Option.isNone ((data frame words.length (Encoding.wordList width words++suffix) [] none).head?) = true := by simp [data_guard]
  have trace := GuardedLink.success none Option.isNone header payload accepted
  have ticks : (4*words.length+4)+(5*words.length+4+(words.length*(22*width+15)+8)) =
      words.length*(22*width+24)+16 := by ring
  have framing : Encoding.encodeWords width words++suffix =
      Encoding.frameCount words.length (Encoding.wordList width words++suffix) := by
    simp only [Encoding.encodeWords, Encoding.frameCount, List.append_assoc, List.cons_append]
  exact ⟨_,by simpa only [program, payloadProgram, ticks, savedFrame, framing] using trace⟩

theorem execution_decodes (frame : Port → List Bool) (words : List (Controller.Cost.Word width)) (suffix : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countEmpty : frame (some 10)=[])
    (bufferEmpty : frame (some 11)=[]) (savedEmpty : frame (some 12)=[]) :
    ∃ final peak, Execution program ⟨some program.main,bank frame [] (Encoding.encodeWords width words++suffix) []⟩ final
      (words.length*(22*width+24)+16) peak ∧
      Encoding.decodeWords width (final.stk (some 12) ++ false :: final.stk (some 11))=some words ∧
      final.stk (some 0)=suffix ∧ final.stk (some 12)=List.replicate words.length true := by
  obtain ⟨peak,trace⟩ := execution frame words suffix stored countEmpty bufferEmpty savedEmpty
  refine ⟨_,peak,trace,?_,?_,?_⟩
  · have parsed := (Encoding.wordsEncoding width).decode_encode words
    change Encoding.decodeWords width (Encoding.encodeWords width words)=some words at parsed
    simpa [data_at, Encoding.encodeWords, Encoding.frameCount] using parsed
  · simp [data_at]
  · simp [data_at]

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 630 := by
  simpa [program, payloadProgram, restorePayload, loop, body, moveWord, restoreMachine, countMachine,
    ColdInput.readSave, ColdInput.headerMachine, CountLoop.program, GuardedLink.program, StackFrames.relocate,
    WidthReader.program, WidthReader.counterMachine, StackCopy.program, WordReader.program,
    WordReader.cursorMachine, WordReader.reverseMachine, reverseProgram, link] using finiteTM_resident program

end Controller.Complexity.WordListReader
