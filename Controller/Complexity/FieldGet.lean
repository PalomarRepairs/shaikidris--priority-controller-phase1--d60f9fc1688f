module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordSelect

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Source-preserving binary-indexed reads of the five persistent state
fields in banks21..25. The finite program copies the framed field, consumes
its actual count header, selects one word and clears all traversal workspace. -/
namespace Controller.Complexity.FieldGet
open StackMachine WordReader
open scoped BigOperators

def field (slot : Fin 5) : Fin 31 := ⟨21+slot.val,by omega⟩

theorem field_ne (slot : Fin 5) (work : Fin 31) (small : work.val<21) :
    (some (field slot) : Port) ≠ some work := by
  intro equal
  have values := congrArg Fin.val (Option.some.inj equal)
  change 21+slot.val=work.val at values
  omega

def copyPorts (slot : Fin 5) : Option Bool ↪ Port :=
  StackFrames.threePorts (some (field slot)) (some 0) (some 2) (field_ne slot 0 (by decide)) (field_ne slot 2 (by decide)) (by decide)

theorem copyPorts_apply (slot : Fin 5) (port : Option Bool) : copyPorts slot port=
    (match port with | none => some (field slot) | some false => some 0 | some true => some 2) := rfl

def copyMachine (slot : Fin 5) := StackFrames.relocate (copyPorts slot) StackCopy.program
def program (slot : Fin 5) := link (link (copyMachine slot) (ColdInput.readSave 10)) WordSelect.program

theorem copy_execution (slot : Fin 5) (input : Port → List Bool) (packet : List Bool)
    (stored : input (some (field slot))=packet) (source : input (some 0)=[]) (scratch : input (some 2)=[]) :
    ∃ peak, Execution (copyMachine slot) ⟨some (copyMachine slot).main,input⟩
      ⟨none,Function.update input (some 0) packet⟩ (5*packet.length+4) peak := by
  obtain ⟨peak,trace⟩ := StackCopy.ready_execution (copyPorts slot) input (by simpa only [copyPorts_apply] using scratch)
  exact ⟨peak,by simpa only [copyMachine,StackFrames.relocate,copyPorts_apply,stored,source,List.append_nil] using trace⟩

theorem saved_output (input : Port → List Bool) (count : Nat) (status word : List Bool) :
    WordSelect.output (Function.update input (some 10) (List.replicate count true)) status word=WordSelect.output input status word := by
  funext address
  simp only [WordSelect.output,WordSkip.reader_at,Function.update_apply]
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases ht : address=some 2 <;> by_cases hn : address=some 10 <;> simp_all

theorem saved_selected (input : Port → List Bool) (words : List (List Bool)) (index : List Bool) :
    WordSelect.selected (Function.update input (some 10) (List.replicate words.length true)) words index=WordSelect.selected input words index := by
  unfold WordSelect.selected
  split <;> exact saved_output input words.length _ _

theorem execution (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (index : List Bool)
    (stored : input (some (field slot))=Encoding.frameCount words.length words.flatten)
    (widthStored : input (some 8)=List.replicate width true) (indexStored : input (some 3)=index)
    (widths : ∀ word ∈ words, word.length=width)
    (status : input none=[]) (source : input (some 0)=[]) (wordWork : input (some 1)=[]) (scratch : input (some 2)=[])
    (counter : input (some 4)=[]) (temporary : input (some 5)=[]) (working : input (some 6)=[]) (mode : input (some 7)=[])
    (countClean : input (some 10)=[]) (bound : input (some 16)=[]) (binaryScratch : input (some 17)=[]) :
    ∃ ticks peak, Execution (program slot) ⟨some (program slot).main,input⟩
      ⟨none,WordSelect.selected input words index⟩ ticks peak ∧
      ticks ≤ 5*(Encoding.frameCount words.length words.flatten).length+index.length*(11*words.length+33)+
        words.length*(16*width+26)+14*width+56 := by
  obtain ⟨copyPeak,copying⟩ := copy_execution slot input _ stored source scratch
  have reading := ColdInput.read_save_execution input 10 (by decide) (by decide) (by decide) words.length words.flatten [] countClean
  have entry : bank input [] (Encoding.frameCount words.length words.flatten) []=
      Function.update input (some 0) (Encoding.frameCount words.length words.flatten) := by
    funext address
    by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
      by_cases ht : address=some 2 <;> simp_all [WordSkip.reader_at]
  have next : bank (Function.update input (some 10) (List.replicate words.length true)) [] words.flatten []=
      WordSkip.data (Function.update input (some 10) (List.replicate words.length true)) 0 words.flatten := by
    funext address
    by_cases hn : address=some 4 <;> simp_all [WordSkip.reader_at,WordSkip.data_at]
  rw [entry,next] at reading
  obtain ⟨selectTicks,selectPeak,selecting,selectBound⟩ := WordSelect.execution
    (Function.update input (some 10) (List.replicate words.length true)) width words index
    (by simpa using widthStored) (by simp) (by simpa using indexStored) widths
    (by simpa using temporary) (by simpa using working) (by simpa using mode)
    (by simpa using bound) (by simpa using binaryScratch)
  rw [saved_selected] at selecting
  have trace := (copying.link reading).link selecting
  have identity : (5*(Encoding.frameCount words.length words.flatten).length+4)+(4*words.length+4)+
      (index.length*(11*words.length+33)+words.length*(16*width+22)+14*width+48)=
      5*(Encoding.frameCount words.length words.flatten).length+index.length*(11*words.length+33)+
        words.length*(16*width+26)+14*width+56 := by ring
  exact ⟨_,_,trace,by omega⟩

def size (input : Port → List Bool) : Nat := ∑ port : Port,(input port).length

theorem total_polynomial (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (index : List Bool)
    (stored : input (some (field slot))=Encoding.frameCount words.length words.flatten)
    (widthStored : input (some 8)=List.replicate width true) (indexStored : input (some 3)=index)
    (widths : ∀ word ∈ words, word.length=width)
    (status : input none=[]) (source : input (some 0)=[]) (wordWork : input (some 1)=[]) (scratch : input (some 2)=[])
    (counter : input (some 4)=[]) (temporary : input (some 5)=[]) (working : input (some 6)=[]) (mode : input (some 7)=[])
    (countClean : input (some 10)=[]) (bound : input (some 16)=[]) (binaryScratch : input (some 17)=[]) :
    ∃ ticks peak, Execution (program slot) ⟨some (program slot).main,input⟩
      ⟨none,WordSelect.selected input words index⟩ ticks peak ∧
      ticks ≤ 27*(size input)^2+78*size input+56 ∧ peak ≤ 27*(size input)^2+79*size input+56 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution slot input width words index stored widthStored indexStored widths status source wordWork scratch
    counter temporary working mode countClean bound binaryScratch
  have cell (port : Port) : (input port).length ≤ size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have packetBound : (Encoding.frameCount words.length words.flatten).length ≤ size input := by simpa only [stored] using cell (some (field slot))
  have countBound : words.length ≤ size input := by
    have framed : words.length ≤ (Encoding.frameCount words.length words.flatten).length := by simp [Encoding.frameCount]
    omega
  have wBound : width ≤ size input := by simpa only [widthStored,List.length_replicate] using cell (some 8)
  have indexBound : index.length ≤ size input := by simpa only [indexStored] using cell (some 3)
  have indexProduct := Nat.mul_le_mul indexBound (Nat.add_le_add_right (Nat.mul_le_mul_left 11 countBound) 33)
  have wordProduct := Nat.mul_le_mul countBound (Nat.add_le_add_right (Nat.mul_le_mul_left 16 wBound) 26)
  have identity : 5*size input+size input*(11*size input+33)+size input*(16*size input+26)+14*size input+56=
      27*(size input)^2+78*size input+56 := by ring
  have bounded : ticks ≤ 27*(size input)^2+78*size input+56 := by rw [← identity]; omega
  have space := trace.peak_le
  change peak ≤ size input+ticks at space
  exact ⟨ticks,peak,trace,bounded,by omega⟩

theorem resident (slot : Fin 5) : (∑ label, statementSize (tmStatement ((program slot).code label))) ≤ 1548 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident (program slot)

theorem mapped_flatten (words : List (Controller.Cost.Word width)) :
    (words.map (fun word => Encoding.bits width word.val)).flatten=Encoding.wordList width words := by
  rfl

def native_output (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (index : Controller.Cost.Word width) : Port → List Bool :=
  if valid : index.val<words.length then WordSelect.output input [] (Encoding.bits width words[index.val].val) else WordSelect.output input [false] []

theorem native_selected (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (index : Controller.Cost.Word width) :
    WordSelect.selected input (words.map (fun word => Encoding.bits width word.val)) (Encoding.bits width index.val)=native_output input words index := by
  simp only [WordSelect.selected,Encoding.value_bits width index.val index.isLt,List.length_map,native_output]
  split <;> simp only [List.getElem_map]

theorem native_observation (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (index : Controller.Cost.Word width) :
    Option.isNone ((native_output input words index none).head?)=(words[index.val]?).isSome ∧
    ∀ value, words[index.val]?=some value → Encoding.decodeWord width (native_output input words index (some 1))=some value := by
  by_cases valid : index.val<words.length
  · simp only [native_output,dite_eq_left valid,WordSelect.output,bank_counter,bank_word,List.head?_nil,Option.isNone_none,
      List.getElem?_eq_getElem valid,Option.isSome_some,Option.some.injEq,true_and]
    intro value equal
    rw [← equal]
    exact (Encoding.wordEncoding width).decode_encode words[index.val]
  · simp [native_output,valid,WordSelect.output,bank_counter]

theorem encoded_total (slot : Fin 5) (input : Port → List Bool) (words : List (Controller.Cost.Word width)) (index : Controller.Cost.Word width)
    (stored : input (some (field slot))=Encoding.encodeWords width words)
    (widthStored : input (some 8)=List.replicate width true) (indexStored : input (some 3)=Encoding.bits width index.val)
    (status : input none=[]) (source : input (some 0)=[]) (wordWork : input (some 1)=[]) (scratch : input (some 2)=[])
    (counter : input (some 4)=[]) (temporary : input (some 5)=[]) (working : input (some 6)=[]) (mode : input (some 7)=[])
    (countClean : input (some 10)=[]) (bound : input (some 16)=[]) (binaryScratch : input (some 17)=[]) :
    ∃ ticks peak, Execution (program slot) ⟨some (program slot).main,input⟩
      ⟨none,native_output input words index⟩ ticks peak ∧
      ticks ≤ 27*(size input)^2+78*size input+56 ∧ peak ≤ 27*(size input)^2+79*size input+56 := by
  have widths : ∀ word ∈ words.map (fun item => Encoding.bits width item.val), word.length=width := by
    intro word member
    obtain ⟨item,_,rfl⟩ := List.mem_map.mp member
    exact Encoding.bits_length width item.val
  have packet : input (some (field slot))=Encoding.frameCount (words.map (fun item => Encoding.bits width item.val)).length
      (words.map (fun item => Encoding.bits width item.val)).flatten := by
    simpa only [List.length_map,mapped_flatten,Encoding.encodeWords] using stored
  simpa only [native_selected] using total_polynomial slot input width (words.map (fun item => Encoding.bits width item.val))
    (Encoding.bits width index.val) packet widthStored indexStored widths status source wordWork scratch counter temporary working mode countClean bound binaryScratch

end Controller.Complexity.FieldGet
