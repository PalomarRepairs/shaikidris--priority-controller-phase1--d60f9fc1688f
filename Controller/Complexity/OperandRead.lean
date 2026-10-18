module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.PcFetch

public import Mathlib.Tactic.FinCases

public import Mathlib.Tactic.Ring

@[expose] public section

/-! A fixed-position operand read copies the fetched payload, seeds a count of
at most two preceding words, executes the skip/read and clears copied source.
The decoded instruction supplies the literal in-range position premise; saved
operand/count/tag banks and all other physical banks are preserved. -/
namespace Controller.Complexity.OperandRead
open StackMachine WordReader
open scoped BigOperators

def work : List Port := [none,some 0,some 1,some 2,some 4]

structure Ready (input : Port → List Bool) (width : Nat) (words : List (List Bool)) : Prop where
  payload : input (some 11)=words.flatten
  stored : input (some 8)=List.replicate width true
  widths : ∀ word ∈ words, word.length=width
  clear : ∀ port ∈ work, input port=[]

def counter (input : Port → List Bool) (count : Nat) := Function.update input (some 4) (List.replicate count true)

def seed (position : Fin 3) : Program (Fin 31) (Fin 3) where
  main := 0
  code label := if before : label.val<position.val then .push (some 4) true ⟨label.val+1,by omega⟩ else .halt

theorem seed_execution (input : Port → List Bool) (position : Fin 3) :
    ∃ peak, Execution (seed position) ⟨some (seed position).main,counter input 0⟩
      ⟨none,counter input position.val⟩ (position.val+1) peak := by
  fin_cases position
  · have last : step (seed 0) ⟨some (seed 0).main,counter input 0⟩=some ⟨none,counter input 0⟩ := rfl
    exact ⟨_,Execution.cons last (Execution.refl _)⟩
  · have first : step (seed 1) ⟨some (seed 1).main,counter input 0⟩=some ⟨some 1,counter input 1⟩ := by
      simp [step,seed,instructionStep,counter]
    have last : step (seed 1) ⟨some 1,counter input 1⟩=some ⟨none,counter input 1⟩ := rfl
    exact ⟨_,Execution.cons first (Execution.cons last (Execution.refl _))⟩
  · have first : step (seed 2) ⟨some (seed 2).main,counter input 0⟩=some ⟨some 1,counter input 1⟩ := by
      simp [step,seed,instructionStep,counter]
    have second : step (seed 2) ⟨some 1,counter input 1⟩=some ⟨some 2,counter input 2⟩ := by
      simp [step,seed,instructionStep,counter]
    have last : step (seed 2) ⟨some 2,counter input 2⟩=some ⟨none,counter input 2⟩ := rfl
    exact ⟨_,Execution.cons first (Execution.cons second (Execution.cons last (Execution.refl _)))⟩

def copyPorts : Option Bool ↪ Port := StackFrames.threePorts (some 11) (some 0) (some 2) (by decide) (by decide) (by decide)
theorem copyPorts_apply (port : Option Bool) : copyPorts port=(match port with | none => some 11 | some false => some 0 | some true => some 2) := rfl

def copyMachine := StackFrames.relocate copyPorts StackCopy.program
def reading := link WordSkip.program WidthReader.program
def program (position : Fin 3) := link (link (link copyMachine (seed position)) reading) (StackClear.program (some 0 : Port))

theorem split_execution (input : Port → List Bool) (width : Nat) (position : Fin 3) (left : List (List Bool)) (word : List Bool) (right : List (List Bool))
    (payload : input (some 11)=left.flatten++(word++right.flatten)) (stored : input (some 8)=List.replicate width true)
    (positionLength : left.length=position.val) (widths : ∀ item ∈ left, item.length=width) (wordWidth : word.length=width)
    (clean : ∀ port ∈ work, input port=[]) :
    ∃ peak, Execution (program position) ⟨some (program position).main,input⟩
      ⟨none,Function.update input (some 1) word⟩
      (5*(left.flatten++(word++right.flatten)).length+right.flatten.length+position.val*(15*width+16)+14*width+21) peak := by
  let source := left.flatten++(word++right.flatten)
  obtain ⟨copyPeak,copying⟩ := StackCopy.ready_execution copyPorts input (by simpa only [copyPorts_apply] using clean (some 2) (by simp [work]))
  change Execution copyMachine _ _ _ _ at copying
  have copyEnd : Function.update input (copyPorts (some false)) (input (copyPorts none)++input (copyPorts (some false)))=
      Function.update input (some 0) source := by simp [copyPorts_apply,payload,clean (some 0) (by simp [work]),source]
  rw [copyEnd] at copying
  simp only [copyPorts_apply,payload] at copying
  obtain ⟨seedPeak,seeding⟩ := seed_execution (Function.update input (some 0) source) position
  have seedStart : counter (Function.update input (some 0) source) 0=Function.update input (some 0) source := by
    funext address
    by_cases same : address=some 4 <;> simp_all [counter,clean (some 4) (by simp [work])]
  have seedEnd : counter (Function.update input (some 0) source) position.val=WordSkip.data input left.length source := by
    funext address
    have status := clean none (by simp [work])
    have wordClean := clean (some 1) (by simp [work])
    have scratch := clean (some 2) (by simp [work])
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
      by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> simp_all [counter,WordSkip.data_at]
  rw [seedStart,seedEnd] at seeding
  obtain ⟨skipPeak,skipping⟩ := WordSkip.execution input width left (word++right.flatten) stored widths
  have readingWord := WidthReader.execution (Function.update input (some 4) []) word right.flatten (by simpa [wordWidth] using stored)
  have scan := skipping.link readingWord
  obtain ⟨clearPeak,clearing⟩ := StackClear.ready_execution (bank (Function.update input (some 4) []) [] right.flatten word) (some 0)
  have endpoint : Function.update (bank (Function.update input (some 4) []) [] right.flatten word) (some 0) []=Function.update input (some 1) word := by
    funext address
    have status := clean none (by simp [work])
    have sourceClean := clean (some 0) (by simp [work])
    have scratch := clean (some 2) (by simp [work])
    have counterClean := clean (some 4) (by simp [work])
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
      by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> simp_all [WordSkip.reader_at]
  rw [endpoint] at clearing
  simp only [bank_source] at clearing
  have trace := ((copying.link seeding).link scan).link clearing
  have ticks : ((5*source.length+4)+(position.val+1))+
      ((left.length*(15*width+15)+2)+(14*word.length+12))+(right.flatten.length+2)=
      5*source.length+right.flatten.length+position.val*(15*width+16)+14*width+21 := by
    rw [wordWidth,positionLength]
    ring
  exact ⟨_,by simpa only [program,reading,WordSkip.data,List.replicate_zero,ticks,source] using trace⟩

def size (input : Port → List Bool) : Nat := ∑ port : Port,(input port).length

theorem execution (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (position : Fin 3)
    (valid : position.val<words.length) (ready : Ready input width words) :
    ∃ ticks peak, Execution (program position) ⟨some (program position).main,input⟩
      ⟨none,Function.update input (some 1) words[position.val]⟩ ticks peak ∧ ticks ≤ 50*size input+53 ∧ peak ≤ 51*size input+53 := by
  let left := words.take position.val
  let right := words.drop (position.val+1)
  let word := words[position.val]
  have positionLength : left.length=position.val := by simp [left,Nat.min_eq_left (Nat.le_of_lt valid)]
  have split : words=left++word::right := by dsimp [left,word,right]; rw [← List.drop_eq_getElem_cons valid,List.take_append_drop]
  have source : words.flatten=left.flatten++(word++right.flatten) := by conv_lhs => rw [split,List.flatten_append,List.flatten_cons]
  have widths : ∀ item ∈ left, item.length=width := by intro item member; exact ready.widths item (List.mem_of_mem_take member)
  have wordWidth := ready.widths word (List.getElem_mem valid)
  obtain ⟨peak,trace⟩ := split_execution input width position left word right (by rw [← source]; exact ready.payload)
    ready.stored positionLength widths wordWidth ready.clear
  rw [← source] at trace
  have cell (port : Port) : (input port).length ≤ size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have payloadBound : words.flatten.length ≤ size input := by simpa only [ready.payload] using cell (some 11)
  have wBound : width ≤ size input := by simpa only [ready.stored,List.length_replicate] using cell (some 8)
  have suffixBound : right.flatten.length ≤ words.flatten.length := by
    have mass := congrArg List.length source
    simp only [List.length_append] at mass
    omega
  have positionBound : position.val ≤ 2 := by omega
  have product := Nat.mul_le_mul_right (15*width+16) positionBound
  have bound : 5*words.flatten.length+right.flatten.length+position.val*(15*width+16)+14*width+21 ≤ 50*size input+53 := by omega
  have space := trace.peak_le
  change peak ≤ size input+(5*words.flatten.length+right.flatten.length+position.val*(15*width+16)+14*width+21) at space
  exact ⟨_,peak,trace,bound,by omega⟩

theorem encoded_total (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (position : Fin 3) (valid : position.val<words.length)
    (payload : input (some 11)=Encoding.wordList width words) (stored : input (some 8)=List.replicate width true)
    (clean : ∀ port ∈ work, input port=[]) :
    ∃ ticks peak, Execution (program position) ⟨some (program position).main,input⟩
      ⟨none,Function.update input (some 1) (Encoding.bits width words[position.val].val)⟩ ticks peak ∧
      ticks ≤ 50*size input+53 ∧ peak ≤ 51*size input+53 := by
  have ready : Ready input width (FieldSetNative.bits words) := {
    payload := by simpa only [FieldSetNative.bits,FieldGet.mapped_flatten] using payload
    stored := stored
    widths := by
      intro word member
      obtain ⟨item,_,rfl⟩ := List.mem_map.mp member
      exact Encoding.bits_length width item.val
    clear := clean }
  simpa only [FieldSetNative.bits,List.getElem_map] using execution input width (FieldSetNative.bits words) position (by simpa [FieldSetNative.bits] using valid) ready

theorem resident (position : Fin 3) : (∑ label, statementSize (tmStatement ((program position).code label))) ≤ 702 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident (program position)

end Controller.Complexity.OperandRead
