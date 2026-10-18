module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.IndexPlan
public import Controller.Complexity.WordSkip

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Binary-indexed selection from a stored fixed-width payload. A range
check guards counter construction, prefix scanning and the final word read.
Both branches execute cleanup of the copied payload and its unary count. -/
namespace Controller.Complexity.WordSelect
open StackMachine WordReader
open scoped BigOperators
abbrev data := WordSkip.data

def scan := link WordSkip.program WidthReader.program
def selectProgram := GuardedLink.program IndexPlan.program scan none Option.isNone
def cleanup := link (StackClear.program (some 0 : Port)) (StackClear.program (some 10 : Port))
def program := link selectProgram cleanup

def output (frame : Port → List Bool) (status word : List Bool) : Port → List Bool :=
  bank (Function.update (Function.update frame (some 4) []) (some 10) []) status [] word

theorem cleanup_execution (input : Port → List Bool) :
    ∃ peak, Execution cleanup ⟨some cleanup.main,input⟩
      ⟨none,Function.update (Function.update input (some 0) []) (some 10) []⟩
      ((input (some 0)).length+(input (some 10)).length+4) peak := by
  obtain ⟨sourcePeak,sourceRun⟩ := StackClear.ready_execution input (some 0)
  obtain ⟨countPeak,countRun⟩ := StackClear.ready_execution (Function.update input (some 0) []) (some 10)
  simp only [Function.update_of_ne (show (some 10 : Port) ≠ some 0 by decide)] at countRun
  have ticks : ((input (some 0)).length+2)+((input (some 10)).length+2)=
      (input (some 0)).length+(input (some 10)).length+4 := by omega
  exact ⟨_,by simpa only [cleanup,ticks] using sourceRun.link countRun⟩

theorem clean_output (frame : Port → List Bool) (status source word : List Bool) :
    Function.update (Function.update (bank (Function.update frame (some 4) []) status source word) (some 0) []) (some 10) []=
      output frame status word := by
  funext address
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases ht : address=some 2 <;> by_cases hn : address=some 10 <;> simp_all [output,WordSkip.reader_at]

theorem planned_output (frame : Port → List Bool) (source index : List Bool) (count : Nat)
    (inRange : Encoding.value index<count) :
    IndexPlan.result (data frame 0 source) index count=data frame (Encoding.value index) source := by
  funext address
  by_cases hc : address=none <;> by_cases hn : address=some 4 <;>
    simp_all [IndexPlan.result,WordSkip.data_at]

theorem scan_execution (frame : Port → List Bool) (width : Nat) (left : List (List Bool)) (word : List Bool) (right : List (List Bool))
    (stored : frame (some 8)=List.replicate width true) (widths : ∀ item ∈ left, item.length=width) (wordWidth : word.length=width) :
    ∃ peak, Execution scan ⟨some scan.main,data frame left.length (left.flatten++(word++right.flatten))⟩
      ⟨none,bank (Function.update frame (some 4) []) [] right.flatten word⟩
      (left.length*(15*width+15)+14*width+14) peak := by
  obtain ⟨skipPeak,skipping⟩ := WordSkip.execution frame width left (word++right.flatten) stored widths
  have reading := WidthReader.execution (Function.update frame (some 4) []) word right.flatten (by simpa [wordWidth] using stored)
  have trace := skipping.link reading
  have ticks : (left.length*(15*width+15)+2)+(14*word.length+12)=left.length*(15*width+15)+14*width+14 := by rw [wordWidth]; omega
  exact ⟨_,by simpa only [scan,WordSkip.data,List.replicate_zero,ticks] using trace⟩

theorem success_execution (frame : Port → List Bool) (width count : Nat)
    (left : List (List Bool)) (word : List Bool) (right : List (List Bool)) (index : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countStored : frame (some 10)=List.replicate count true)
    (indexStored : frame (some 3)=index) (atIndex : Encoding.value index=left.length)
    (cardinality : count=left.length+1+right.length) (widths : ∀ item ∈ left, item.length=width) (wordWidth : word.length=width)
    (temporary : frame (some 5)=[]) (working : frame (some 6)=[]) (mode : frame (some 7)=[])
    (bound : frame (some 16)=[]) (scratch : frame (some 17)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,data frame 0 (left.flatten++(word++right.flatten))⟩
      ⟨none,output frame [] word⟩ ticks peak ∧
      ticks ≤ index.length*(11*count+33)+7*count+left.length*(15*width+15)+14*width+right.flatten.length+48 := by
  let source := left.flatten++(word++right.flatten)
  have inRange : Encoding.value index<count := by omega
  obtain ⟨planTicks,planPeak,planning,planBound⟩ := IndexPlan.execution (data frame 0 source) index count
    (by simpa [WordSkip.data_at] using indexStored) (by simpa [WordSkip.data_at] using countStored)
    (by simp [WordSkip.data_at]) (by simp [WordSkip.data_at]) (by simpa [WordSkip.data_at] using bound)
    (by simp [WordSkip.data_at]) (by simpa [WordSkip.data_at] using temporary)
    (by simpa [WordSkip.data_at] using working) (by simpa [WordSkip.data_at] using mode)
    (by simpa [WordSkip.data_at] using scratch)
  rw [planned_output frame source index count inRange,atIndex] at planning
  obtain ⟨scanPeak,scanning⟩ := scan_execution frame width left word right stored widths wordWidth
  have trace := GuardedLink.success none Option.isNone planning scanning (by simp [WordSkip.data_at])
  obtain ⟨clearPeak,clearing⟩ := cleanup_execution (bank (Function.update frame (some 4) []) [] right.flatten word)
  rw [clean_output] at clearing
  have countLength : (bank (Function.update frame (some 4) []) [] right.flatten word (some 10)).length=count := by
    simp [WordSkip.reader_at,countStored]
  simp only [bank_source,countLength] at clearing
  have joined := trace.link clearing
  refine ⟨planTicks+(left.length*(15*width+15)+14*width+14)+(right.flatten.length+count+4),_,joined,?_⟩
  omega

theorem failure_execution (frame : Port → List Bool) (count : Nat) (source index : List Bool)
    (countStored : frame (some 10)=List.replicate count true) (indexStored : frame (some 3)=index)
    (outOfRange : ¬Encoding.value index<count)
    (temporary : frame (some 5)=[]) (working : frame (some 6)=[]) (mode : frame (some 7)=[])
    (bound : frame (some 16)=[]) (scratch : frame (some 17)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,data frame 0 source⟩
      ⟨none,output frame [false] []⟩ ticks peak ∧
      ticks ≤ index.length*(11*count+33)+7*count+source.length+35 := by
  obtain ⟨planTicks,planPeak,planning,planBound⟩ := IndexPlan.execution (data frame 0 source) index count
    (by simpa [WordSkip.data_at] using indexStored) (by simpa [WordSkip.data_at] using countStored)
    (by simp [WordSkip.data_at]) (by simp [WordSkip.data_at]) (by simpa [WordSkip.data_at] using bound)
    (by simp [WordSkip.data_at]) (by simpa [WordSkip.data_at] using temporary)
    (by simpa [WordSkip.data_at] using working) (by simpa [WordSkip.data_at] using mode)
    (by simpa [WordSkip.data_at] using scratch)
  have rejected : IndexPlan.result (data frame 0 source) index count=bank (Function.update frame (some 4) []) [false] source [] := by
    funext address
    by_cases hc : address=none <;> by_cases hn : address=some 4 <;>
      simp_all [IndexPlan.result,WordSkip.data_at,WordSkip.reader_at]
  rw [rejected] at planning
  have trace := GuardedLink.failure scan none Option.isNone planning (by simp [bank_counter])
  obtain ⟨clearPeak,clearing⟩ := cleanup_execution (bank (Function.update frame (some 4) []) [false] source [])
  rw [clean_output] at clearing
  have countLength : (bank (Function.update frame (some 4) []) [false] source [] (some 10)).length=count := by
    simp [WordSkip.reader_at,countStored]
  simp only [bank_source,countLength] at clearing
  have joined := trace.link clearing
  exact ⟨_,_,joined,by omega⟩

theorem flatten_length (width : Nat) (words : List (List Bool)) (widths : ∀ word ∈ words, word.length=width) :
    words.flatten.length=words.length*width := by
  induction words with
  | nil => simp
  | cons word words ih =>
    have head := widths word (by simp)
    have tail := ih (by intro item member; exact widths item (by simp [member]))
    simp only [List.flatten_cons,List.length_append,List.length_cons,head,tail,Nat.add_mul,Nat.one_mul]
    omega

def selected (frame : Port → List Bool) (words : List (List Bool)) (index : List Bool) : Port → List Bool :=
  if valid : Encoding.value index<words.length then output frame [] words[Encoding.value index] else output frame [false] []

theorem execution (frame : Port → List Bool) (width : Nat) (words : List (List Bool)) (index : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countStored : frame (some 10)=List.replicate words.length true)
    (indexStored : frame (some 3)=index) (widths : ∀ word ∈ words, word.length=width)
    (temporary : frame (some 5)=[]) (working : frame (some 6)=[]) (mode : frame (some 7)=[])
    (bound : frame (some 16)=[]) (scratch : frame (some 17)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,data frame 0 words.flatten⟩
      ⟨none,selected frame words index⟩ ticks peak ∧
      ticks ≤ index.length*(11*words.length+33)+words.length*(16*width+22)+14*width+48 := by
  by_cases valid : Encoding.value index<words.length
  · let left := words.take (Encoding.value index)
    let right := words.drop (Encoding.value index+1)
    let word := words[Encoding.value index]
    have leftLength : left.length=Encoding.value index := by simp [left,Nat.min_eq_left (Nat.le_of_lt valid)]
    have split : words=left++word::right := by
      dsimp [left,word,right]
      rw [← List.drop_eq_getElem_cons valid,List.take_append_drop]
    have cardinality : words.length=left.length+1+right.length := by
      have eq := congrArg List.length split
      simp only [List.length_append,List.length_cons] at eq
      omega
    have source : words.flatten=left.flatten++(word++right.flatten) := by
      conv_lhs => rw [split,List.flatten_append,List.flatten_cons]
    have leftWidths : ∀ item ∈ left, item.length=width := by
      intro item member
      exact widths item (List.mem_of_mem_take member)
    have rightWidths : ∀ item ∈ right, item.length=width := by
      intro item member
      exact widths item (List.mem_of_mem_drop member)
    have wordWidth : word.length=width := widths word (List.getElem_mem valid)
    obtain ⟨ticks,peak,trace,timeBound⟩ := success_execution frame width words.length left word right index
      stored countStored indexStored leftLength.symm cardinality leftWidths wordWidth temporary working mode bound scratch
    rw [← source] at trace
    have final : selected frame words index=output frame [] word := by simp only [selected,dite_eq_left valid]; rfl
    rw [← final] at trace
    have leftBound : left.length ≤ words.length := by omega
    have rightBound : right.length ≤ words.length := by omega
    have product := Nat.mul_le_mul_right (15*width+15) leftBound
    have rightMass := flatten_length width right rightWidths
    have suffixBound := Nat.mul_le_mul_right width rightBound
    have identity : 7*words.length+words.length*(15*width+15)+14*width+words.length*width+48=
        words.length*(16*width+22)+14*width+48 := by ring
    exact ⟨ticks,peak,trace,by omega⟩
  · obtain ⟨ticks,peak,trace,timeBound⟩ := failure_execution frame words.length words.flatten index
      countStored indexStored valid temporary working mode bound scratch
    have final : selected frame words index=output frame [false] [] := by simp only [selected,dite_eq_right valid]
    rw [← final] at trace
    have mass := flatten_length width words widths
    have product := Nat.mul_le_mul_left words.length (show width+7 ≤ 16*width+22 by omega)
    have identity : 7*words.length+words.length*width=words.length*(width+7) := by ring
    exact ⟨ticks,peak,trace,by omega⟩

def size (frame : Port → List Bool) (words : List (List Bool)) : Nat := ∑ port : Port,(data frame 0 words.flatten port).length

theorem total_polynomial (frame : Port → List Bool) (width : Nat) (words : List (List Bool)) (index : List Bool)
    (stored : frame (some 8)=List.replicate width true) (countStored : frame (some 10)=List.replicate words.length true)
    (indexStored : frame (some 3)=index) (widths : ∀ word ∈ words, word.length=width)
    (temporary : frame (some 5)=[]) (working : frame (some 6)=[]) (mode : frame (some 7)=[])
    (bound : frame (some 16)=[]) (scratch : frame (some 17)=[]) :
    ∃ ticks peak, Execution program ⟨some program.main,data frame 0 words.flatten⟩
      ⟨none,selected frame words index⟩ ticks peak ∧
      ticks ≤ 27*(size frame words)^2+69*size frame words+48 ∧ peak ≤ 27*(size frame words)^2+70*size frame words+48 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution frame width words index stored countStored indexStored widths temporary working mode bound scratch
  have cell (port : Port) : (data frame 0 words.flatten port).length ≤ size frame words :=
    Finset.single_le_sum (f := fun address : Port => (data frame 0 words.flatten address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have indexBound : index.length ≤ size frame words := by simpa [WordSkip.data_at,indexStored] using cell (some 3)
  have nBound : words.length ≤ size frame words := by simpa [WordSkip.data_at,countStored] using cell (some 10)
  have wBound : width ≤ size frame words := by simpa [WordSkip.data_at,stored] using cell (some 8)
  have product := Nat.mul_le_mul indexBound (Nat.add_le_add_right (Nat.mul_le_mul_left 11 nBound) 33)
  have payload := Nat.mul_le_mul nBound (Nat.add_le_add_right (Nat.mul_le_mul_left 16 wBound) 22)
  have identity : size frame words*(11*size frame words+33)+size frame words*(16*size frame words+22)+14*size frame words+48=
      27*(size frame words)^2+69*size frame words+48 := by ring
  have bounded : ticks ≤ 27*(size frame words)^2+69*size frame words+48 := by rw [← identity]; omega
  have space := trace.peak_le
  change peak ≤ size frame words+ticks at space
  exact ⟨ticks,peak,trace,bounded,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 1377 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.WordSelect
