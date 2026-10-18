module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedSourceRead
public import Controller.Cost.SharedChannelStore

public import Mathlib.Tactic.FinCases

@[expose] public section

/-! A root occurrence is fetched by the output cursor, retained in a reusable
header slot, and tested against the stored healthy table. The cursor is parked
under the selector traversal's frames. -/
namespace Controller.Extensions.ResolvedRootRead
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

def indexedCode (width base : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width base), .add 0 0 3, .load 1 0]

@[simp] theorem indexedCode_length : (indexedCode width base).length = 3 := rfl

theorem indexed_execution (program : Program width 8) (state : State width 8)
    (entry base cursor : Nat) (value : Word width)
    (stored : state.heap[base+cursor]? = some value)
    (held : state.reg 3 = word width cursor)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry+3 < 2^width) (heapFits : state.heap.size < 2^width)
    (present : SharedRootRead.BlockAt program entry (indexedCode width base)) :
    ∃ final, Execution program state final 3 state.liveWords ∧
      final.reg 1 = value ∧ final.heap = state.heap ∧ final.stack = state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry+3) ∧ final.halted = false ∧
      (∀ i : Fin 8, i ≠ 0 → i ≠ 1 → final.reg i = state.reg i) := by
  have bound := (Array.getElem?_eq_some_iff.mp stored).1
  have cell := (Array.getElem?_eq_some_iff.mp stored).2
  obtain ⟨s1,t1,p1,v1,h1,st1,o1,r1,f1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry base 0 state position running (by omega)
      (by simpa [indexedCode] using present 0 (by simp))
  obtain ⟨s2,t2,p2,v2,h2,st2,o2,r2,f2⟩ :=
    EnumerationSteps.add_execution program s1 (entry+1) 0 0 3 p1 r1 (by omega)
      (by simpa [indexedCode] using present 1 (by simp))
  have address : (s2.reg 0).val = base+cursor := by
    rw [v2,v1,f1 3 (by decide),held]
    simp only [word,Nat.mod_eq_of_lt (by omega : base<2^width),
      Nat.mod_eq_of_lt (by omega : cursor<2^width),Nat.mod_eq_of_lt (by omega : base+cursor<2^width)]
  obtain ⟨final,t3,p3,v3,h3,st3,o3,r3,f3⟩ :=
    EnumerationSteps.load_execution program s2 (entry+2) 1 0
      (by simpa only [Nat.add_assoc,Nat.reduceAdd] using p2) r2 (by omega)
      (by simpa only [address,h2,h1] using bound)
      (by simpa [indexedCode] using present 2 (by simp))
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords,h1,st1,o1]
  have l2 : s2.liveWords = state.liveWords := by simp only [State.liveWords,h2,st2,o2,h1,st1,o1]
  refine ⟨final, by simpa only [l1,l2,Nat.max_self] using t1.append (t2.append t3), ?_,
    h3.trans (h2.trans h1),st3.trans (st2.trans st1),o3.trans (o2.trans o1),
    by simpa only [Nat.add_assoc,Nat.reduceAdd] using p3,r3,?_⟩
  · calc
      final.reg 1 = state.heap[base+cursor] := by simpa only [address,h2,h1] using v3
      _ = value := cell
  · intro i h0 h1; rw [f3 i h1,f2 i h0,f1 i h0]

def storeCode (width slot : Nat) : List (Instruction width 8) :=
  [.constant 0 (word width slot), .store 0 1]

@[simp] theorem storeCode_length : (storeCode width slot).length = 2 := rfl

theorem store_execution (program : Program width 8) (state : State width 8)
    (entry slot : Nat) (value : Word width) (held : state.reg 1 = value)
    (valid : slot < state.heap.size)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry+2 < 2^width) (heapFits : state.heap.size < 2^width)
    (present : SharedRootRead.BlockAt program entry (storeCode width slot)) :
    ∃ final, Execution program state final 2 state.liveWords ∧
      final.heap = state.heap.set slot value ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (entry+2) ∧ final.halted = false ∧
      (∀ i : Fin 8, i ≠ 0 → final.reg i = state.reg i) := by
  obtain ⟨middle,first,pc,reg,heap,stack,output,active,frame⟩ :=
    SharedEvaluationReclaim.constant_execution program entry slot 0 state position running (by omega)
      (by simpa [storeCode] using present 0 (by simp))
  obtain ⟨final,last,fh,fs,fo,fp,fr,ff⟩ :=
    SharedChannelStore.execution program middle (entry+1) slot value pc active (by omega) (by omega)
      (by simpa only [heap] using valid) reg ((frame 1 (by decide)).trans held)
      (by intro i; fin_cases i; simpa [SharedChannelStore.code,storeCode] using present 1 (by simp))
  have live : middle.liveWords = state.liveWords := by simp only [State.liveWords,heap,stack,output]
  exact ⟨final,by simpa only [live,Nat.max_self] using first.append last,
    by simpa only [heap] using fh,fs.trans stack,fo.trans output,
    by simpa only [Nat.add_assoc,Nat.reduceAdd] using fp,fr,
    fun i hi => (congrFun ff i).trans (frame i hi)⟩

def code (width rootBase slot healthyBase rejected : Nat) : List (Instruction width 8) :=
  indexedCode width rootBase ++ (storeCode width slot ++
    ([.push 3, .constant 3 (word width slot), .constant 1 (word width healthyBase)] ++
    (SharedRootRead.code width ++ [.branchZero 1 (word width rejected)])))

@[simp] theorem code_length : (code width rootBase slot healthyBase rejected).length = 12 := by simp [code]

theorem execution (program : Program width 8) (state : State width 8)
    (entry rootBase slot healthyBase rejected cursor root : Nat) (healthy : Bool)
    (stored : state.heap[rootBase+cursor]? = some (word width root))
    (healthyStored : state.heap[healthyBase+root]? = some (boolWord width healthy))
    (valid : slot < state.heap.size) (separate : healthyBase+root ≠ slot)
    (held : state.reg 3 = word width cursor)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry+12 < 2^width) (heapFits : state.heap.size < 2^width)
    (present : SharedRootRead.BlockAt program entry (code width rootBase slot healthyBase rejected)) :
    ∃ final, Execution program state final 12 (state.liveWords+1) ∧
      final.heap = state.heap.set slot (word width root) ∧
      final.stack = word width cursor :: state.stack ∧ final.output = state.output ∧
      final.pc = word width (if healthy then entry+12 else rejected) ∧ final.halted = false := by
  have firstAt := block_left program entry _ _ present
  have afterFirst := block_right program entry _ _ present
  simp only [indexedCode_length] at afterFirst
  have storeAt := block_left program (entry+3) _ _ afterFirst
  have afterStore := block_right program (entry+3) _ _ afterFirst
  simp only [storeCode_length,Nat.add_assoc,Nat.reduceAdd] at afterStore
  have setupAt := block_left program (entry+5) _ _ afterStore
  have afterSetup := block_right program (entry+5) _ _ afterStore
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.add_assoc] at afterSetup
  have readAt := block_left program (entry+8) _ _ afterSetup
  have branchAt := block_right program (entry+8) _ _ afterSetup
  simp only [SharedRootRead.code_length,Nat.add_assoc,Nat.reduceAdd] at branchAt
  obtain ⟨read,t1,v1,h1,st1,o1,p1,r1,f1⟩ :=
    indexed_execution program state entry rootBase cursor _ stored held position running (by omega) heapFits firstAt
  obtain ⟨saved,t2,h2,st2,o2,p2,r2,f2⟩ :=
    store_execution program read (entry+3) slot _ v1 (by simpa only [h1] using valid)
      p1 r1 (by omega) (by simpa only [h1] using heapFits) storeAt
  obtain ⟨pushed,t3,p3,h3,st3,o3,r3,f3,l3⟩ :=
    EnumerationSteps.push_execution program saved (entry+5) 3
      (by simpa only [Nat.add_assoc,Nat.reduceAdd] using p2) r2 (by omega)
      (by simpa using setupAt 0 (by simp))
  obtain ⟨s4,t4,p4,v4,h4,st4,o4,r4,f4⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry+6) slot 3 pushed p3 r3 (by omega)
      (by simpa using setupAt 1 (by simp))
  obtain ⟨s5,t5,p5,v5,h5,st5,o5,r5,f5⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry+7) healthyBase 1 s4 p4 r4 (by omega)
      (by simpa using setupAt 2 (by simp))
  have heap5 : s5.heap = state.heap.set slot (word width root) := by
    simpa only [h1] using h5.trans (h4.trans (h3.trans h2))
  have source5 : s5.heap[slot]? = some (word width root) := by simp [heap5,valid]
  have health5 : s5.heap[healthyBase+root]? = some (boolWord width healthy) := by
    simp only [heap5,Array.getElem?_set,ite_eq_right (Ne.symm separate)]; exact healthyStored
  obtain ⟨tested,t6,_,observed,_,_,h6,st6,o6,p6,r6,_⟩ :=
    SharedRootRead.execution program s5 slot healthyBase root (entry+8) healthy
      ((f5 3 (by decide)).trans v4) v5 (Array.getElem?_eq_some_iff.mp source5).1 (by omega)
      (Array.getElem?_eq_some_iff.mp source5).2 (Array.getElem?_eq_some_iff.mp health5).1
      (by have := (Array.getElem?_eq_some_iff.mp healthyStored).1; omega)
      (Array.getElem?_eq_some_iff.mp health5).2 p5 r5 (by omega) readAt
  have branch : ∃ final, Execution program tested final 1 tested.liveWords ∧
      final.pc = word width (if healthy then entry+12 else rejected) ∧
      final.heap = tested.heap ∧ final.stack = tested.stack ∧ final.output = tested.output ∧ final.halted = false := by
    cases healthy with
    | false =>
      obtain ⟨final,tr,pc,h,s,o,r,_⟩ := EnumerationSteps.branch_taken program tested (entry+11) rejected 1
        (by simpa only [Nat.add_assoc,Nat.reduceAdd] using p6) r6 (by omega)
        (by rw [observed]; simp [boolWord,word]) (by simpa using branchAt 0 (by simp))
      exact ⟨final,tr,pc,h,s,o,r⟩
    | true =>
      obtain ⟨final,tr,pc,h,s,o,r,_⟩ := EnumerationSteps.branch_skipped program tested (entry+11) rejected 1
        (by simpa only [Nat.add_assoc,Nat.reduceAdd] using p6) r6 (by omega)
        (by rw [observed]; simp [boolWord,word,Nat.mod_eq_of_lt (by omega : 1<2^width)])
        (by simpa using branchAt 0 (by simp))
      exact ⟨final,tr,pc,h,s,o,r⟩
  obtain ⟨final,t7,fp,fh,fs,fo,fr⟩ := branch
  have readLive : read.liveWords = state.liveWords := by simp only [State.liveWords,h1,st1,o1]
  have savedLive : saved.liveWords = state.liveWords := by simp only [State.liveWords,h2,st2,o2,h1,st1,o1,Array.size_set]
  have live4 : s4.liveWords = pushed.liveWords := by simp only [State.liveWords,h4,st4,o4]
  have live5 : s5.liveWords = pushed.liveWords := by simp only [State.liveWords,h5,st5,o5,h4,st4,o4]
  have live6 : tested.liveWords = pushed.liveWords := by simp only [State.liveWords,h6,st6,o6,h5,st5,o5,h4,st4,o4]
  refine ⟨final, ?_, fh.trans (h6.trans heap5), ?_,
    fo.trans (o6.trans (o5.trans (o4.trans (o3.trans (o2.trans o1))))),fp,fr⟩
  · simpa only [readLive,savedLive,live4,live5,live6,l3,Nat.max_self,
      Nat.max_eq_right (Nat.le_succ _)] using t1.append (t2.append (t3.append (t4.append (t5.append (t6.append t7)))))
  · rw [fs,st6,st5,st4,st3,f2 3 (by decide),f1 3 (by decide) (by decide),held,st2,st1]

end Controller.Extensions.ResolvedRootRead
