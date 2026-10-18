module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.FieldGrowth
public import Controller.Complexity.HeapCapacity

public import Mathlib.Tactic.Ring

@[expose] public section

/-! Native heap allocation checks the actual field count strictly below word
capacity before appending. Failed capacity retains the original heap. Copying,
comparison, growth, commit and both cleanup branches are executed and charged. -/
namespace Controller.Complexity.HeapAllocate
open StackMachine WordReader
open scoped BigOperators

def grow := link FieldGrowth.backBody (FieldGrowth.finish (1 : Fin 5))
def guarded := GuardedLink.program HeapCapacity.program grow none Option.isNone
def program := link (link (FieldPrepare.program (1 : Fin 5)) guarded) WordSelect.cleanup

def result (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (replacement : List Bool) : Port → List Bool :=
  if words.length<2^width then FieldReplace.output input 1
    (Encoding.frameCount (words.length+1) (words.flatten++replacement))
  else WordSelect.output input [false] []

theorem capacity_execution (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (replacement : List Bool)
    (ready : FieldGrowth.Ready 1 input width words replacement) :
    ∃ ticks peak, Execution HeapCapacity.program ⟨some HeapCapacity.program.main,FieldPrepare.prepared input words⟩
      ⟨none,Function.update (FieldPrepare.prepared input words) none (if words.length<2^width then [] else [false])⟩ ticks peak ∧
      ticks ≤ width*(4*words.length+10)+6*words.length+16 := by
  have bound := ready.clear (some 16) (by simp [FieldSet.work])
  have scratch := ready.clear (some 17) (by simp [FieldSet.work])
  apply HeapCapacity.ready_execution
  all_goals simp_all [FieldPrepare.prepared,FieldSet.prepared,FieldSet.frame,WordSkip.data_at,ready.widthStored]

theorem grow_execution (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (replacement : List Bool)
    (ready : FieldGrowth.Ready 1 input width words replacement) :
    ∃ peak, Execution grow ⟨some grow.main,FieldPrepare.prepared input words⟩
      ⟨none,FieldReplace.output input 1 (Encoding.frameCount (words.length+1) (words.flatten++replacement))⟩
      ((Encoding.frameCount words.length words.flatten).length+9*replacement.length+4*words.flatten.length+2*words.length+20) peak := by
  obtain ⟨bodyPeak,collecting⟩ := FieldGrowth.back_body (FieldPrepare.frame input words) words.flatten replacement
    (by simpa [FieldSet.frame] using ready.replacementStored)
  obtain ⟨finishPeak,finishing⟩ := FieldGrowth.finish_execution (FieldPrepare.frame input words) 1 words.length (words.flatten++replacement).reverse
    (by simp [FieldSet.frame])
  rw [FieldPrepare.frame_output,List.reverse_reverse] at finishing
  have oldLength : (FieldPrepare.frame input words (some (FieldGet.field 1))).length=(Encoding.frameCount words.length words.flatten).length := by
    simp [FieldSet.frame,FieldGet.field_ne 1 10 (by decide),ready.packet]
  rw [oldLength,List.length_reverse,List.length_append] at finishing
  have trace := collecting.link finishing
  rw [← FieldPrepare.prefix_ready 1 input width words ready.toReady] at trace
  have ticks : (7*replacement.length+2*words.flatten.length+8)+
      ((Encoding.frameCount words.length words.flatten).length+2*(words.flatten.length+replacement.length)+2*words.length+12)=
      (Encoding.frameCount words.length words.flatten).length+9*replacement.length+4*words.flatten.length+2*words.length+20 := by omega
  exact ⟨_,by simpa only [grow,ticks] using trace⟩

theorem execution (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (replacement : List Bool)
    (ready : FieldGrowth.Ready 1 input width words replacement) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,result input width words replacement⟩ ticks peak ∧
      ticks ≤ 6*(Encoding.frameCount words.length words.flatten).length+12*words.length+
        width*(4*words.length+19)+4*words.flatten.length+48 := by
  obtain ⟨preparePeak,preparing⟩ := FieldPrepare.execution 1 input width words ready.toReady
  obtain ⟨capacityTicks,capacityPeak,checking,capacityBound⟩ := capacity_execution input width words replacement ready
  have status : FieldPrepare.prepared input words none=[] := by simp [FieldSet.prepared,WordSkip.data_at]
  by_cases valid : words.length<2^width
  · have clean : Function.update (FieldPrepare.prepared input words) none ([] : List Bool)=FieldPrepare.prepared input words := by
      funext address
      by_cases same : address=none <;> simp_all
    simp only [ite_eq_left valid,clean] at checking
    obtain ⟨growPeak,growing⟩ := grow_execution input width words replacement ready
    have trace := GuardedLink.success none Option.isNone checking growing (by simp only [status,List.head?_nil,Option.isNone_none])
    obtain ⟨clearPeak,clearing⟩ := WordSelect.cleanup_execution (FieldReplace.output input 1 (Encoding.frameCount (words.length+1) (words.flatten++replacement)))
    rw [FieldSet.clean_replacement] at clearing
    have emptySource : FieldReplace.output input 1 (Encoding.frameCount (words.length+1) (words.flatten++replacement)) (some 0)=[] := by
      simp [FieldReplace.output,WordSelect.output,bank_source,Ne.symm (FieldGet.field_ne 1 0 (by decide))]
    have emptyCount : FieldReplace.output input 1 (Encoding.frameCount (words.length+1) (words.flatten++replacement)) (some 10)=[] := by
      simp [FieldReplace.output,WordSelect.output,WordSkip.reader_at,Ne.symm (FieldGet.field_ne 1 10 (by decide))]
    simp only [emptySource,emptyCount,List.length_nil,Nat.zero_add] at clearing
    have joined := (preparing.link trace).link clearing
    have final : result input width words replacement=FieldReplace.output input 1 (Encoding.frameCount (words.length+1) (words.flatten++replacement)) := by simp only [result,ite_eq_left valid]
    rw [← final] at joined
    have identity : 4*words.length+8+(width*(4*words.length+10)+6*words.length+16)+
        (9*width+4*words.flatten.length+2*words.length+20)+4=
        12*words.length+width*(4*words.length+19)+4*words.flatten.length+48 := by ring
    exact ⟨_,_,joined,by rw [ready.replacementWidth]; omega⟩
  · simp only [ite_eq_right valid] at checking
    have rejected : Function.update (FieldPrepare.prepared input words) none [false]=
        bank (Function.update (FieldPrepare.frame input words) (some 4) []) [false] words.flatten [] := by
      funext address
      by_cases hc : address=none <;> by_cases hn : address=some 4 <;>
        simp_all [FieldSet.prepared,WordSkip.data_at,WordSkip.reader_at]
    rw [rejected] at checking
    have trace := GuardedLink.failure grow none Option.isNone checking (by simp [bank_counter])
    obtain ⟨clearPeak,clearing⟩ := WordSelect.cleanup_execution (bank (Function.update (FieldPrepare.frame input words) (some 4) []) [false] words.flatten [])
    rw [WordSelect.clean_output,FieldPrepare.saved_output] at clearing
    have countLength : (bank (Function.update (FieldPrepare.frame input words) (some 4) []) [false] words.flatten [] (some 10)).length=words.length := by
      simp [WordSkip.reader_at,FieldSet.frame]
    simp only [bank_source,countLength] at clearing
    have joined := (preparing.link trace).link clearing
    have final : result input width words replacement=WordSelect.output input [false] [] := by simp only [result,ite_eq_right valid]
    rw [← final] at joined
    have payload : words.flatten.length ≤ (Encoding.frameCount words.length words.flatten).length := by
      simp only [Encoding.frameCount,List.length_append,List.length_replicate,List.length_cons]; omega
    have extra : width*(4*words.length+10) ≤ width*(4*words.length+19) := Nat.mul_le_mul_left width (by omega)
    exact ⟨_,_,joined,by omega⟩

theorem total_polynomial (input : Port → List Bool) (width : Nat) (words : List (List Bool)) (replacement : List Bool)
    (ready : FieldGrowth.Ready 1 input width words replacement) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,result input width words replacement⟩ ticks peak ∧
      ticks ≤ 4*(FieldGrowth.size input)^2+41*FieldGrowth.size input+48 ∧ peak ≤ 4*(FieldGrowth.size input)^2+42*FieldGrowth.size input+48 := by
  obtain ⟨ticks,peak,trace,timeBound⟩ := execution input width words replacement ready
  have cell (port : Port) : (input port).length ≤ FieldGrowth.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ port)
  have packetBound : (Encoding.frameCount words.length words.flatten).length ≤ FieldGrowth.size input := by simpa only [ready.packet] using cell (some (FieldGet.field 1))
  have wBound : width ≤ FieldGrowth.size input := by simpa only [ready.widthStored,List.length_replicate] using cell (some 8)
  have packetLength : (Encoding.frameCount words.length words.flatten).length=words.length+1+words.flatten.length := by
    simp only [Encoding.frameCount,List.length_append,List.length_replicate,List.length_cons]; omega
  have nBound : words.length ≤ FieldGrowth.size input := by omega
  have product := Nat.mul_le_mul wBound (Nat.add_le_add_right (Nat.mul_le_mul_left 4 nBound) 19)
  have identity : 6*FieldGrowth.size input+12*FieldGrowth.size input+FieldGrowth.size input*(4*FieldGrowth.size input+19)+4*FieldGrowth.size input+48=
      4*(FieldGrowth.size input)^2+41*FieldGrowth.size input+48 := by ring
  have bounded : ticks ≤ 4*(FieldGrowth.size input)^2+41*FieldGrowth.size input+48 := by rw [← identity]; omega
  have space := trace.peak_le
  change peak ≤ FieldGrowth.size input+ticks at space
  exact ⟨ticks,peak,trace,bounded,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 855 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul,WordBound.Label,WordBound.BodyLabel] using finiteTM_resident program

end Controller.Complexity.HeapAllocate
