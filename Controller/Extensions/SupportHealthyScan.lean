module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedDetectorAssembly
public import Controller.Cost.EnumerationSteps

@[expose] public section

/-! Before bounded-support search, the declared root occurrences are scanned
against the computed healthy table. If every root is healthy-one, the driver
can enter the selector phase without enumerating any channel supports. -/
namespace Controller.Extensions.SupportHealthyScan
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly

def nodeCode (width cursor healthyBase needed : Nat) : List (Instruction width 8) :=
  [.constant 3 (word width cursor),.constant 1 (word width healthyBase)] ++
    (SharedRootRead.code width ++ [.branchZero 1 (word width needed)])

@[simp] theorem nodeCode_length : (nodeCode width cursor healthyBase needed).length = 6 := rfl

theorem node_execution (resident : Program width 8) (state : State width 8)
    (entry cursor healthyBase needed root : Nat) (healthy : Bool)
    (source : state.heap[cursor]? = some (word width root))
    (stored : state.heap[healthyBase+root]? = some (boolWord width healthy))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry+6<2^width) (heapFits : state.heap.size<2^width)
    (present : SharedRootRead.BlockAt resident entry (nodeCode width cursor healthyBase needed)) :
    ∃ final, Execution resident state final 6 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if healthy then entry+6 else needed) ∧ final.halted = false := by
  have setupAt := block_left resident entry _ _ present
  have afterSetup := block_right resident entry _ _ present
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd] at afterSetup
  have readAt := block_left resident (entry+2) _ _ afterSetup
  have branchAt := block_right resident (entry+2) _ _ afterSetup
  simp only [SharedRootRead.code_length,Nat.add_assoc,Nat.reduceAdd] at branchAt
  obtain ⟨s1,t1,p1,v1,h1,st1,o1,r1,f1⟩ :=
    SharedEvaluationReclaim.constant_execution resident entry cursor 3 state position running (by omega)
      (by simpa using setupAt 0 (by simp))
  obtain ⟨s2,t2,p2,v2,h2,st2,o2,r2,f2⟩ :=
    SharedEvaluationReclaim.constant_execution resident (entry+1) healthyBase 1 s1 p1 r1 (by omega)
      (by simpa using setupAt 1 (by simp))
  have source2 : s2.heap[cursor]? = some (word width root) := by simpa only [h2,h1] using source
  have stored2 : s2.heap[healthyBase+root]? = some (boolWord width healthy) := by simpa only [h2,h1] using stored
  obtain ⟨tested,t3,_,observed,_,_,h3,st3,o3,p3,r3,_⟩ :=
    SharedRootRead.execution resident s2 cursor healthyBase root (entry+2) healthy
      ((f2 3 (by decide)).trans v1) v2 (Array.getElem?_eq_some_iff.mp source2).1
      (by have := (Array.getElem?_eq_some_iff.mp source).1; omega)
      (Array.getElem?_eq_some_iff.mp source2).2 (Array.getElem?_eq_some_iff.mp stored2).1
      (by have := (Array.getElem?_eq_some_iff.mp stored).1; omega)
      (Array.getElem?_eq_some_iff.mp stored2).2
      (by simpa only [Nat.add_assoc,Nat.reduceAdd] using p2) r2 (by omega) readAt
  have branch : ∃ final, Execution resident tested final 1 tested.liveWords ∧
      final.pc = word width (if healthy then entry+6 else needed) ∧
      final.heap = tested.heap ∧ final.stack = tested.stack ∧ final.output = tested.output ∧ final.halted = false := by
    cases healthy with
    | false =>
      obtain ⟨final,tr,pc,h,s,o,r,_⟩ := EnumerationSteps.branch_taken resident tested (entry+5) needed 1
        (by simpa only [Nat.add_assoc,Nat.reduceAdd] using p3) r3 (by omega)
        (by rw [observed]; simp [boolWord,word]) (by simpa using branchAt 0 (by simp))
      exact ⟨final,tr,pc,h,s,o,r⟩
    | true =>
      obtain ⟨final,tr,pc,h,s,o,r,_⟩ := EnumerationSteps.branch_skipped resident tested (entry+5) needed 1
        (by simpa only [Nat.add_assoc,Nat.reduceAdd] using p3) r3 (by omega)
        (by rw [observed]; simp [boolWord,word,Nat.mod_eq_of_lt (by omega : 1<2^width)])
        (by simpa using branchAt 0 (by simp))
      exact ⟨final,tr,pc,h,s,o,r⟩
  obtain ⟨final,t4,fp,fh,fs,fo,fr⟩ := branch
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords,h1,st1,o1]
  have l2 : s2.liveWords = state.liveWords := by simp only [State.liveWords,h2,st2,o2,h1,st1,o1]
  have l3 : tested.liveWords = state.liveWords := by simp only [State.liveWords,h3,st3,o3,h2,st2,o2,h1,st1,o1]
  exact ⟨final,by simpa only [l1,l2,l3,Nat.max_self] using t1.append (t2.append (t3.append t4)),
    fh.trans (h3.trans (h2.trans h1)),fs.trans (st3.trans (st2.trans st1)),
    fo.trans (o3.trans (o2.trans o1)),fp,fr⟩

def code (width cursor healthyBase needed count : Nat) : List (Instruction width 8) :=
  (List.range count).flatMap fun i => nodeCode width (cursor+i) healthyBase needed

@[simp] theorem code_length : (code width cursor healthyBase needed count).length = 6*count := by
  simp [code,List.length_flatMap]; omega

theorem code_succ : code width cursor healthyBase needed (count+1) =
    nodeCode width cursor healthyBase needed ++ code width (cursor+1) healthyBase needed count := by
  simp only [code,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,Nat.add_zero]
  congr 1
  apply List.flatMap_congr
  intro i member
  congr 1
  omega

theorem execution (resident : Program width 8) (state : State width 8)
    (entry cursor healthyBase needed : Nat) (observations : List Nat) (healthy : Nat → Bool)
    (source : ∀ i (below : i<observations.length), state.heap[cursor+i]? = some (word width observations[i]))
    (stored : ∀ root ∈ observations, state.heap[healthyBase+root]? = some (boolWord width (healthy root)))
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry+6*observations.length<2^width) (heapFits : state.heap.size<2^width)
    (present : SharedRootRead.BlockAt resident entry (code width cursor healthyBase needed observations.length)) :
    ∃ final ticks, Execution resident state final ticks state.liveWords ∧ ticks ≤ 6*observations.length ∧
      final.heap = state.heap ∧ final.stack = state.stack ∧ final.output = state.output ∧
      final.pc = word width (if observations.all healthy then entry+6*observations.length else needed) ∧ final.halted = false := by
  induction observations generalizing entry cursor state with
  | nil => exact ⟨state,0,Execution.refl _,by simp,rfl,rfl,rfl,by simpa using position,running⟩
  | cons root rest ih =>
    rw [List.length_cons,code_succ] at present
    have firstAt := block_left resident entry _ _ present
    have lastAt := block_right resident entry _ _ present
    simp only [nodeCode_length] at lastAt
    obtain ⟨middle,first,heap,stack,output,pc,active⟩ :=
      node_execution resident state entry cursor healthyBase needed root (healthy root)
        (by have cell := source 0 (by simp); change state.heap[cursor+0]? = some (word width root) at cell; simpa using cell)
        (stored root (by simp)) position running (by simp only [List.length_cons] at room; omega) heapFits firstAt
    cases value : healthy root with
    | false =>
      exact ⟨middle,6,first,by simp,heap,stack,output,by simpa only [value,List.all_cons,Bool.false_and,Bool.false_eq_true,ite_false] using pc,active⟩
    | true =>
      obtain ⟨final,ticks,last,time,fh,fs,fo,fp,fr⟩ :=
        ih middle (entry+6) (cursor+1)
          (by intro i below; have cell := source (i+1) (by simp; omega)
              simpa only [heap,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cell)
          (by intro root member; simpa only [heap] using stored root (by simp [member]))
          (by simpa only [value,ite_true] using pc) active
          (by simp only [List.length_cons] at room; omega) (by simpa only [heap] using heapFits) lastAt
      have live : middle.liveWords = state.liveWords := by simp only [State.liveWords,heap,stack,output]
      refine ⟨final,6+ticks,by simpa only [live,Nat.max_self] using first.append last,
        by simp only [List.length_cons]; omega,fh.trans heap,fs.trans stack,fo.trans output,?_,fr⟩
      simpa only [List.all_cons,value,Bool.true_and,List.length_cons,Nat.mul_add,Nat.mul_one,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fp

end Controller.Extensions.SupportHealthyScan
