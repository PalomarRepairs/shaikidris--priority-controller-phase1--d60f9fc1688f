module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.FieldPrepare

@[expose] public section

/-! Executed prepend and append of an exact-width word to a persistent field.
The original replacement operand is retained. Count growth, copying, old-field
erasure and framing are charged; native allocation capacity is a separate guard. -/
namespace Controller.Complexity.FieldGrowth
open StackMachine WordReader
open scoped BigOperators

structure Ready (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (replacement : List Bool)
    extends FieldPrepare.Ready slot input width words where
  replacementStored : input (some 27)=replacement
  replacementWidth : replacement.length=width

def frontBody := StackMachine.link (link FieldReplace.copyReplacement WordPrefix.moveWord) FieldReplace.moveRest
def backBody := StackMachine.link (link FieldReplace.moveRest FieldReplace.copyReplacement) WordPrefix.moveWord
def finish (slot : Fin 5) := link UnaryAdjust.increment (FieldCommit.program slot)
def prepend (slot : Fin 5) := link (link (FieldPrepare.program slot) frontBody) (finish slot)
def append (slot : Fin 5) := link (link (FieldPrepare.program slot) backBody) (finish slot)

theorem front_body (input : Port → List Bool) (source replacement : List Bool) (stored : input (some 27)=replacement) :
    ∃ peak, Execution frontBody ⟨some frontBody.main,WordPrefix.data input 0 source []⟩
      ⟨none,WordPrefix.data input 0 [] (replacement++source).reverse⟩ (7*replacement.length+2*source.length+8) peak := by
  obtain ⟨copyPeak,copying⟩ := FieldReplace.copy_execution input source [] replacement stored
  obtain ⟨movePeak,moving⟩ := WordPrefix.move_word_execution input 0 source replacement []
  obtain ⟨restPeak,restRun⟩ := FieldReplace.rest_execution input source replacement.reverse
  simp only [List.append_nil] at moving
  have trace := (copying.link moving).link restRun
  have ticks : (5*replacement.length+4)+(2*replacement.length+2)+(2*source.length+2)=7*replacement.length+2*source.length+8 := by omega
  exact ⟨_,by simpa only [frontBody,List.reverse_append,ticks] using trace⟩

theorem back_body (input : Port → List Bool) (source replacement : List Bool) (stored : input (some 27)=replacement) :
    ∃ peak, Execution backBody ⟨some backBody.main,WordPrefix.data input 0 source []⟩
      ⟨none,WordPrefix.data input 0 [] (source++replacement).reverse⟩ (7*replacement.length+2*source.length+8) peak := by
  obtain ⟨restPeak,restRun⟩ := FieldReplace.rest_execution input source []
  simp only [List.append_nil] at restRun
  obtain ⟨copyPeak,copying⟩ := FieldReplace.copy_execution input [] source.reverse replacement stored
  obtain ⟨movePeak,moving⟩ := WordPrefix.move_word_execution input 0 [] replacement source.reverse
  have trace := (restRun.link copying).link moving
  have ticks : (2*source.length+2)+(5*replacement.length+4)+(2*replacement.length+2)=7*replacement.length+2*source.length+8 := by omega
  exact ⟨_,by simpa only [backBody,List.reverse_append,ticks] using trace⟩

theorem finish_execution (input : Port → List Bool) (slot : Fin 5) (count : Nat) (buffer : List Bool)
    (stored : input (some 10)=List.replicate count true) :
    ∃ peak, Execution (finish slot) ⟨some (finish slot).main,WordPrefix.data input 0 [] buffer⟩
      ⟨none,FieldReplace.output input slot (Encoding.frameCount (count+1) buffer.reverse)⟩
      ((input (some (FieldGet.field slot))).length+2*buffer.length+2*count+12) peak := by
  obtain ⟨incrementPeak,incrementing⟩ := UnaryAdjust.increment_execution (WordPrefix.data input 0 [] buffer) count (by simpa [WordPrefix.data_at] using stored)
  rw [FieldPrepare.count_update] at incrementing
  obtain ⟨commitPeak,committing⟩ := FieldCommit.ready_execution
    (WordPrefix.data (Function.update input (some 10) (List.replicate (count+1) true)) 0 [] buffer) slot (count+1) buffer
    (by simp [WordPrefix.data_at]) (by simp [WordPrefix.data_at])
  rw [FieldReplace.commit_output,FieldPrepare.output_count] at committing
  have oldLength : (WordPrefix.data (Function.update input (some 10) (List.replicate (count+1) true)) 0 [] buffer
      (some (FieldGet.field slot))).length=(input (some (FieldGet.field slot))).length := by
    simp [WordPrefix.data_at,FieldGet.field_ne slot 0 (by decide),FieldGet.field_ne slot 1 (by decide),FieldGet.field_ne slot 2 (by decide),
      FieldGet.field_ne slot 4 (by decide),FieldGet.field_ne slot 10 (by decide),FieldGet.field_ne slot 20 (by decide)]
  rw [oldLength] at committing
  have ticks : 2+((input (some (FieldGet.field slot))).length+2*buffer.length+2*(count+1)+8)=
      (input (some (FieldGet.field slot))).length+2*buffer.length+2*count+12 := by omega
  exact ⟨_,by simpa only [finish,ticks] using incrementing.link committing⟩

theorem prepend_execution (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (replacement : List Bool)
    (ready : Ready slot input width words replacement) :
    ∃ peak, Execution (prepend slot) ⟨some (prepend slot).main,input⟩
      ⟨none,FieldReplace.output input slot (Encoding.frameCount (words.length+1) (replacement++words.flatten))⟩
      (6*(Encoding.frameCount words.length words.flatten).length+6*words.length+9*replacement.length+4*words.flatten.length+28) peak := by
  obtain ⟨preparePeak,preparing⟩ := FieldPrepare.execution slot input width words ready.toReady
  rw [FieldPrepare.prefix_ready slot input width words ready.toReady] at preparing
  obtain ⟨bodyPeak,collecting⟩ := front_body (FieldPrepare.frame input words) words.flatten replacement (by simpa [FieldSet.frame] using ready.replacementStored)
  obtain ⟨finishPeak,finishing⟩ := finish_execution (FieldPrepare.frame input words) slot words.length (replacement++words.flatten).reverse (by simp [FieldSet.frame])
  rw [FieldPrepare.frame_output,List.reverse_reverse] at finishing
  have oldLength : (FieldPrepare.frame input words (some (FieldGet.field slot))).length=(Encoding.frameCount words.length words.flatten).length := by
    simp [FieldSet.frame,FieldGet.field_ne slot 10 (by decide),ready.packet]
  rw [oldLength,List.length_reverse,List.length_append] at finishing
  have trace := (preparing.link collecting).link finishing
  have ticks : (5*(Encoding.frameCount words.length words.flatten).length+4*words.length+8)+
      (7*replacement.length+2*words.flatten.length+8)+
      ((Encoding.frameCount words.length words.flatten).length+2*(replacement.length+words.flatten.length)+2*words.length+12)=
      6*(Encoding.frameCount words.length words.flatten).length+6*words.length+9*replacement.length+4*words.flatten.length+28 := by omega
  exact ⟨_,by simpa only [prepend,ticks] using trace⟩

theorem append_execution (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (replacement : List Bool)
    (ready : Ready slot input width words replacement) :
    ∃ peak, Execution (append slot) ⟨some (append slot).main,input⟩
      ⟨none,FieldReplace.output input slot (Encoding.frameCount (words.length+1) (words.flatten++replacement))⟩
      (6*(Encoding.frameCount words.length words.flatten).length+6*words.length+9*replacement.length+4*words.flatten.length+28) peak := by
  obtain ⟨preparePeak,preparing⟩ := FieldPrepare.execution slot input width words ready.toReady
  rw [FieldPrepare.prefix_ready slot input width words ready.toReady] at preparing
  obtain ⟨bodyPeak,collecting⟩ := back_body (FieldPrepare.frame input words) words.flatten replacement (by simpa [FieldSet.frame] using ready.replacementStored)
  obtain ⟨finishPeak,finishing⟩ := finish_execution (FieldPrepare.frame input words) slot words.length (words.flatten++replacement).reverse (by simp [FieldSet.frame])
  rw [FieldPrepare.frame_output,List.reverse_reverse] at finishing
  have oldLength : (FieldPrepare.frame input words (some (FieldGet.field slot))).length=(Encoding.frameCount words.length words.flatten).length := by
    simp [FieldSet.frame,FieldGet.field_ne slot 10 (by decide),ready.packet]
  rw [oldLength,List.length_reverse,List.length_append] at finishing
  have trace := (preparing.link collecting).link finishing
  have ticks : (5*(Encoding.frameCount words.length words.flatten).length+4*words.length+8)+
      (7*replacement.length+2*words.flatten.length+8)+
      ((Encoding.frameCount words.length words.flatten).length+2*(words.flatten.length+replacement.length)+2*words.length+12)=
      6*(Encoding.frameCount words.length words.flatten).length+6*words.length+9*replacement.length+4*words.flatten.length+28 := by omega
  exact ⟨_,by simpa only [append,ticks] using trace⟩

def size (input : Port → List Bool) : Nat := ∑ port : Port,(input port).length

theorem growth_bound (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (replacement : List Bool)
    (ready : Ready slot input width words replacement) :
    6*(Encoding.frameCount words.length words.flatten).length+6*words.length+9*replacement.length+4*words.flatten.length+28 ≤ 25*size input+28 := by
  have cell (port : Port) : (input port).length ≤ size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have packetBound : (Encoding.frameCount words.length words.flatten).length ≤ size input := by simpa only [ready.packet] using cell (some (FieldGet.field slot))
  have replBound : replacement.length ≤ size input := by simpa only [ready.replacementStored] using cell (some 27)
  have packetLength : (Encoding.frameCount words.length words.flatten).length=words.length+1+words.flatten.length := by
    simp only [Encoding.frameCount,List.length_append,List.length_replicate,List.length_cons]; omega
  omega

theorem prepend_resources (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (replacement : List Bool)
    (ready : Ready slot input width words replacement) :
    ∃ ticks peak, Execution (prepend slot) ⟨some (prepend slot).main,input⟩
      ⟨none,FieldReplace.output input slot (Encoding.frameCount (words.length+1) (replacement++words.flatten))⟩ ticks peak ∧
      ticks ≤ 25*size input+28 ∧ peak ≤ 26*size input+28 := by
  obtain ⟨peak,trace⟩ := prepend_execution slot input width words replacement ready
  have timeBound := growth_bound slot input width words replacement ready
  have space := trace.peak_le
  change peak ≤ size input+_ at space
  exact ⟨_,peak,trace,timeBound,by omega⟩

theorem append_resources (slot : Fin 5) (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (replacement : List Bool)
    (ready : Ready slot input width words replacement) :
    ∃ ticks peak, Execution (append slot) ⟨some (append slot).main,input⟩
      ⟨none,FieldReplace.output input slot (Encoding.frameCount (words.length+1) (words.flatten++replacement))⟩ ticks peak ∧
      ticks ≤ 25*size input+28 ∧ peak ≤ 26*size input+28 := by
  obtain ⟨peak,trace⟩ := append_execution slot input width words replacement ready
  have timeBound := growth_bound slot input width words replacement ready
  have space := trace.peak_le
  change peak ≤ size input+_ at space
  exact ⟨_,peak,trace,timeBound,by omega⟩

theorem prepend_resident (slot : Fin 5) : (∑ label, statementSize (tmStatement ((prepend slot).code label))) ≤ 459 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident (prepend slot)

theorem append_resident (slot : Fin 5) : (∑ label, statementSize (tmStatement ((append slot).code label))) ≤ 459 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident (append slot)

end Controller.Complexity.FieldGrowth
