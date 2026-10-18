module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportSearchRun
public import Controller.Cost.SharedCoordinateTable

@[expose] public section

/-! Fetched mask allocation and sentinel construction enter the returning
subset traversal from an arbitrary caller state. Reused zero masks need only
the six-instruction entry block. -/
namespace Controller.Extensions.SupportSearchInit
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly
open Controller.Extensions.SupportSearch

def enterCode (width n capacity : Nat) : List (Instruction width 8) :=
  [.constant 5 (word width 0), .push 5, .constant 3 (word width n), .push 3,
    .constant 3 (word width 0), .constant 5 (word width (min capacity n))]

@[simp] theorem enterCode_length : (enterCode width n capacity).length = 6 := rfl

theorem enter_execution (program : Program width 8) (state : State width 8)
    (entry n capacity : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry+6 < 2^width)
    (present : SharedRootRead.BlockAt program entry (enterCode width n capacity)) :
    ∃ final, Execution program state final 6 (state.liveWords+2) ∧
      final.heap = state.heap ∧ final.stack = word width n :: word width 0 :: state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry+6) ∧ final.halted = false ∧
      final.reg 3 = word width 0 ∧ final.reg 5 = word width (min capacity n) := by
  obtain ⟨s1,t1,p1,v1,h1,st1,o1,r1,f1⟩ :=
    SharedEvaluationReclaim.constant_execution program entry 0 5 state position running (by omega)
      (by simpa [enterCode] using present 0 (by simp))
  obtain ⟨s2,t2,p2,h2,st2,o2,r2,f2,l2⟩ :=
    EnumerationSteps.push_execution program s1 (entry+1) 5 p1 r1 (by omega)
      (by simpa [enterCode] using present 1 (by simp))
  obtain ⟨s3,t3,p3,v3,h3,st3,o3,r3,f3⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry+2) n 3 s2
      (by simpa [Nat.add_assoc] using p2) r2 (by omega)
      (by simpa [enterCode] using present 2 (by simp))
  obtain ⟨s4,t4,p4,h4,st4,o4,r4,f4,l4⟩ :=
    EnumerationSteps.push_execution program s3 (entry+3) 3
      (by simpa [Nat.add_assoc] using p3) r3 (by omega)
      (by simpa [enterCode] using present 3 (by simp))
  obtain ⟨s5,t5,p5,v5,h5,st5,o5,r5,f5⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry+4) 0 3 s4
      (by simpa [Nat.add_assoc] using p4) r4 (by omega)
      (by simpa [enterCode] using present 4 (by simp))
  obtain ⟨final,t6,p6,v6,h6,st6,o6,r6,f6⟩ :=
    SharedEvaluationReclaim.constant_execution program (entry+5) (min capacity n) 5 s5
      (by simpa [Nat.add_assoc] using p5) r5 (by omega)
      (by simpa [enterCode] using present 5 (by simp))
  have l1 : s1.liveWords = state.liveWords := by simp only [State.liveWords,h1,st1,o1]
  have l3 : s3.liveWords = s2.liveWords := by simp only [State.liveWords,h3,st3,o3]
  have l5 : s5.liveWords = s4.liveWords := by simp only [State.liveWords,h5,st5,o5]
  refine ⟨final, ?_, h6.trans (h5.trans (h4.trans (h3.trans (h2.trans h1)))), ?_,
    o6.trans (o5.trans (o4.trans (o3.trans (o2.trans o1)))),
    by simpa only [Nat.add_assoc, Nat.reduceAdd] using p6, r6,
    (f6 3 (by decide)).trans v5, v6⟩
  · have joined := t1.append (t2.append (t3.append (t4.append (t5.append t6))))
    simpa only [l1,l3,l5,l2,l4,Nat.add_assoc,Nat.reduceAdd,
      Nat.max_eq_right (by omega : state.liveWords ≤ state.liveWords+2),
      Nat.max_eq_right (by omega : state.liveWords+1 ≤ state.liveWords+2), Nat.max_self] using joined
  · rw [st6,st5,st4,v3,st3,st2,v1,st1]

def code (width n capacity : Nat) : List (Instruction width 8) :=
  SharedCoordinateTable.code width (List.replicate n (word width 0)) ++ enterCode width n capacity

@[simp] theorem code_length : (code width n capacity).length = 2*n+6 := by simp [code]

theorem execution (program : Program width 8) (state : State width 8)
    (entry n capacity : Nat) (position : state.pc = word width entry)
    (running : state.halted = false) (room : entry+2*n+6 < 2^width)
    (heapFits : state.heap.size+n < 2^width)
    (present : SharedRootRead.BlockAt program entry (code width n capacity)) :
    ∃ final, Execution program state final (2*n+6) (state.liveWords+n+2) ∧
      final.heap = maskHeap state.heap (∅ : Finset (Fin n)) ∧
      final.stack = word width n :: word width 0 :: state.stack ∧
      final.output = state.output ∧ final.pc = word width (entry+2*n+6) ∧ final.halted = false ∧
      final.reg 3 = word width 0 ∧ final.reg 5 = word width (min capacity n) := by
  have firstAt := block_left program entry _ _ present
  have lastAt := block_right program entry _ _ present
  simp only [SharedCoordinateTable.code_length,List.length_replicate] at lastAt
  obtain ⟨allocated,first,ah,ast,ao,ap,ar,_⟩ :=
    SharedCoordinateTable.execution program state (List.replicate n (word width 0)) entry
      position running (by simpa using (show entry+2*n<2^width by omega))
      (by simpa using heapFits) firstAt
  obtain ⟨final,last,fh,fs,fo,fp,fr,fc,fb⟩ :=
    enter_execution program allocated (entry+2*n) n capacity (by simpa using ap) ar (by omega) lastAt
  have live : allocated.liveWords = state.liveWords+n := by
    simp only [State.liveWords,ah,ast,ao,Array.size_append,List.size_toArray,List.length_replicate]; omega
  refine ⟨final, ?_, ?_, by simpa only [ast] using fs, fo.trans ao, fp, fr, fc, fb⟩
  · simpa only [List.length_replicate,live,Nat.max_eq_right (by omega :
      state.liveWords+n ≤ state.liveWords+n+2)] using first.append last
  · rw [fh,ah]
    simp [maskHeap,Controller.Cost.ForestInputStored.withValues,Controller.assignmentOfSet,
      boolWord, List.ofFn_const]

end Controller.Extensions.SupportSearchInit
