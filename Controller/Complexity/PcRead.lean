module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Complexity.WordMove

@[expose] public section

/-! The persistent singleton PC field is read through the actual indexed-field
routine. An empty temporary index selects its sole word; a charged order-
preserving move puts the PC bits in index3 and clears the returned-word bank. -/
namespace Controller.Complexity.PcRead
open StackMachine WordReader
open scoped BigOperators

structure Ready (input : Port → List Bool) (pc : Controller.Cost.Word width) : Prop where
  stored : input (some 8)=List.replicate width true
  pcStored : input (some (FieldGet.field 4))=Encoding.encodeWords width [pc]
  indexEmpty : input (some 3)=[]
  clear : ∀ port ∈ FetchSetup.work, input port=[]

def program := link (FieldGet.program (4 : Fin 5)) (WordMove.program (some 1) (some 3) (some 2))
def output (input : Port → List Bool) (pc : Controller.Cost.Word width) := Function.update input (some 3) (Encoding.bits width pc.val)

theorem getter_output (input : Port → List Bool) (pc : Controller.Cost.Word width) (ready : Ready input pc) :
    WordSelect.selected input [Encoding.bits width pc.val] []=Function.update input (some 1) (Encoding.bits width pc.val) := by
  funext address
  have status := ready.clear none (by simp [FetchSetup.work])
  have source := ready.clear (some 0) (by simp [FetchSetup.work])
  have word := ready.clear (some 1) (by simp [FetchSetup.work])
  have scratch := ready.clear (some 2) (by simp [FetchSetup.work])
  have counter := ready.clear (some 4) (by simp [FetchSetup.work])
  have count := ready.clear (some 10) (by simp [FetchSetup.work])
  by_cases hc : address=none <;> by_cases hs : address=some 0 <;> by_cases hw : address=some 1 <;>
    by_cases ht : address=some 2 <;> by_cases hn : address=some 4 <;> by_cases hb : address=some 10 <;>
      simp_all [WordSelect.selected,Encoding.value,WordSelect.output,WordSkip.reader_at]

theorem execution (input : Port → List Bool) (pc : Controller.Cost.Word width) (ready : Ready input pc) :
    ∃ ticks peak, Execution program ⟨some program.main,input⟩ ⟨none,output input pc⟩ ticks peak ∧
      ticks ≤ 27*(FetchSetup.size input)^2+82*FetchSetup.size input+60 ∧ peak ≤ 27*(FetchSetup.size input)^2+83*FetchSetup.size input+60 := by
  have packet : input (some (FieldGet.field 4))=Encoding.frameCount [Encoding.bits width pc.val].length [Encoding.bits width pc.val].flatten := by
    simpa [Encoding.encodeWords,Encoding.wordList,Encoding.wordEncoding] using ready.pcStored
  have widths : ∀ word ∈ [Encoding.bits width pc.val], word.length=width := by
    intro word member
    simp only [List.mem_singleton] at member
    subst word
    exact Encoding.bits_length width pc.val
  obtain ⟨getTicks,getPeak,getting,getBound,_⟩ := FieldGet.total_polynomial 4 input width [Encoding.bits width pc.val] [] packet ready.stored ready.indexEmpty widths
    (ready.clear _ (by simp [FetchSetup.work])) (ready.clear _ (by simp [FetchSetup.work]))
    (ready.clear _ (by simp [FetchSetup.work])) (ready.clear _ (by simp [FetchSetup.work]))
    (ready.clear _ (by simp [FetchSetup.work])) (ready.clear _ (by simp [FetchSetup.work]))
    (ready.clear _ (by simp [FetchSetup.work])) (ready.clear _ (by simp [FetchSetup.work]))
    (ready.clear _ (by simp [FetchSetup.work])) (ready.clear _ (by simp [FetchSetup.work])) (ready.clear _ (by simp [FetchSetup.work]))
  rw [getter_output input pc ready] at getting
  obtain ⟨movePeak,moving⟩ := WordMove.execution (Function.update input (some 1) (Encoding.bits width pc.val)) (some 1) (some 3) (some 2)
    (by decide) (by decide) (by decide) (by simpa using ready.clear (some 2) (by simp [FetchSetup.work]))
  have final : Function.update (Function.update (Function.update input (some 1) (Encoding.bits width pc.val)) (some 1) []) (some 3)
      ((Function.update input (some 1) (Encoding.bits width pc.val) (some 1))++Function.update input (some 1) (Encoding.bits width pc.val) (some 3))=output input pc := by
    funext address
    have word := ready.clear (some 1) (by simp [FetchSetup.work])
    by_cases hw : address=some 1 <;> by_cases hi : address=some 3 <;> simp_all [output,ready.indexEmpty]
  rw [final] at moving
  simp only [Function.update_self,Encoding.bits_length] at moving
  have trace := getting.link moving
  have cell : (input (some 8)).length ≤ FetchSetup.size input :=
    Finset.single_le_sum (f := fun address : Port => (input address).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some 8))
  have wBound : width ≤ FetchSetup.size input := by simpa only [ready.stored,List.length_replicate] using cell
  change getTicks ≤ 27*(FetchSetup.size input)^2+78*FetchSetup.size input+56 at getBound
  have timeBound : getTicks+(4*width+4) ≤ 27*(FetchSetup.size input)^2+82*FetchSetup.size input+60 := by omega
  have space := trace.peak_le
  change max getPeak movePeak ≤ FetchSetup.size input+(getTicks+(4*width+4)) at space
  exact ⟨_,_,trace,timeBound,by omega⟩

theorem resident : (∑ label, statementSize (tmStatement (program.code label))) ≤ 1620 := by
  simpa only [Fintype.card_sum,Fintype.card_option,Fintype.card_fin,Nat.reduceAdd,Nat.reduceMul] using finiteTM_resident program

end Controller.Complexity.PcRead
