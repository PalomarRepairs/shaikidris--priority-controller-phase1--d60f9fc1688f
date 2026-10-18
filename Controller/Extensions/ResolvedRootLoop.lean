module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.ResolvedRootRead
public import Controller.Extensions.SupportSearchInit
public import Controller.Cost.EnumerationDriverControl

@[expose] public section

/-! The output loop retains one original root cursor under each selector
search. Rejected searches return through the same increment block. -/
namespace Controller.Extensions.ResolvedRootLoop
open Controller.Cost Controller.Cost.RawTransferLoops Controller.Cost.SharedDetectorAssembly
open Controller.Extensions.SupportSearch Controller.Extensions.SupportStream

def advanceCode (width loop : Nat) : List (Instruction width 8) :=
  [.pop 3] ++ EnumerationDriverControl.incrementCode width loop

@[simp] theorem advanceCode_length : (advanceCode width loop).length = 5 := rfl

theorem advance_execution (program : Program width 8) (state : State width 8)
    (entry loop cursor : Nat) (rest : List (Word width))
    (position : state.pc = word width entry) (running : state.halted = false)
    (saved : state.stack = word width cursor :: rest)
    (cursorFits : cursor+1 < 2^width) (room : entry+5 < 2^width)
    (present : SharedRootRead.BlockAt program entry (advanceCode width loop)) :
    ∃ final, Execution program state final 5 state.liveWords ∧
      final.heap = state.heap ∧ final.stack = rest ∧ final.output = state.output ∧
      final.pc = word width loop ∧ final.halted = false ∧ final.reg 3 = word width (cursor+1) := by
  have lastAt := block_right program entry _ _ present
  simp only [List.length_singleton] at lastAt
  obtain ⟨popped,first,pc,reg,heap,stack,output,active,_⟩ :=
    EnumerationSteps.pop_execution program state entry 3 _ rest position running (by omega) saved
      (by simpa only [advanceCode,List.singleton_append,List.getElem?_cons_zero,Nat.add_zero] using
        present 0 (by simp [advanceCode]))
  obtain ⟨final,last,fc,fh,fs,fo,fp,fr,_⟩ :=
    EnumerationDriverControl.increment_execution program popped (entry+1) cursor loop pc active reg cursorFits
      (by omega) lastAt
  have live : popped.liveWords ≤ state.liveWords := Execution.final_storage_le first
  exact ⟨final,by simpa only [Nat.max_eq_left live] using first.append last,
    fh.trans heap,fs.trans stack,fo.trans output,fp,fr,fc⟩

def attemptCode (width rootBase slot healthyBase rejected seek ands : Nat) : List (Instruction width 8) :=
  ResolvedRootRead.code width rootBase slot healthyBase rejected ++
    (SupportSearchInit.enterCode width ands ands ++ EnumerationDriverCode.jump width seek)

@[simp] theorem attemptCode_length :
    (attemptCode width rootBase slot healthyBase rejected seek ands).length = 20 := by
  simp [attemptCode,EnumerationDriverCode.jump]

def Outcome (source : Array (Word width)) (query : Finset (Fin ands) → Option β)
    (found rejected cursor : Nat) (rest : List (Word width)) (final : State width 8) : Option β → Prop
  | none => final.heap = maskHeap source (∅ : Finset (Fin ands)) ∧
      final.stack = word width cursor :: rest ∧ final.pc = word width rejected ∧ final.halted = false
  | some value => (∃ chosen, final.heap = maskHeap source chosen ∧ query chosen = some value) ∧
      (∃ saved, final.stack = saved ++ rest) ∧ final.pc = word width found ∧ final.halted = false

set_option maxHeartbeats 1200000 in
theorem attempt_execution (program : Program width 8) (state : State width 8)
    (before source : Array (Word width)) (query : Finset (Fin ands) → Option β)
    (entry rootBase slot healthyBase rejected seek call found cursor root Q S : Nat) (healthy : Bool)
    (sameSize : before.size = source.size)
    (heapStored : state.heap = maskHeap before (∅ : Finset (Fin ands)))
    (valid : slot < state.heap.size)
    (update : state.heap.set slot (word width root) = maskHeap source (∅ : Finset (Fin ands)))
    (stored : state.heap[rootBase+cursor]? = some (word width root))
    (healthyStored : state.heap[healthyBase+root]? = some (boolWord width healthy))
    (separate : healthyBase+root ≠ slot)
    (held : state.reg 3 = word width cursor)
    (position : state.pc = word width entry) (running : state.halted = false)
    (room : entry+20 < 2^width) (searchRoom : seek+37 < 2^width)
    (heapFits : state.heap.size < 2^width) (limitFits : ands < 2^width)
    (present : SharedRootRead.BlockAt program entry
      (attemptCode width rootBase slot healthyBase rejected seek ands))
    (callback : Callback program source query seek call found Q S)
    (coreAt : SharedRootRead.BlockAt program seek
      (SupportTraversal.endingCode width seek ands source.size call (.constant 0 (word width 0))))
    (returnAt : SharedRootRead.BlockAt program (SupportTraversal.done seek) (EnumerationDriverCode.jump width rejected)) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ (Q+50)*2^ands+27 ∧
      peak ≤ source.size+3*ands+S+state.stack.length+state.output.length+12 ∧ final.output = state.output ∧
      Outcome source query found rejected cursor state.stack final
        (if healthy then (search (fun chosen : List (Fin ands) => query chosen.toFinset)
          ands (List.finRange ands) []).result else none) := by
  have readAt := block_left program entry _ _ present
  have afterRead := block_right program entry _ _ present
  simp only [ResolvedRootRead.code_length] at afterRead
  have initAt := block_left program (entry+12) _ _ afterRead
  have jumpAt := block_right program (entry+12) _ _ afterRead
  simp only [SupportSearchInit.enterCode_length,Nat.add_assoc,Nat.reduceAdd] at jumpAt
  have startLive : state.liveWords = source.size+ands+state.stack.length+state.output.length+9 := by
    simp only [State.liveWords,heapStored,maskHeap_size,sameSize]; omega
  have powers : 1 ≤ 2^ands := Nat.one_le_pow _ _ (by decide)
  obtain ⟨read,first,rh,rs,ro,rp,rr⟩ :=
    ResolvedRootRead.execution program state entry rootBase slot healthyBase rejected cursor root healthy
      stored healthyStored valid separate held position running (by omega) heapFits readAt
  have readHeap : read.heap = maskHeap source (∅ : Finset (Fin ands)) := rh.trans update
  cases healthy with
  | false =>
    exact ⟨read,12,state.liveWords+1,first,by omega,by omega,ro,readHeap,rs,rp,rr⟩
  | true =>
    obtain ⟨initialized,setup,ih,ist,io,ip,ir,ic,ib⟩ :=
      SupportSearchInit.enter_execution program read (entry+12) ands ands rp rr (by omega) initAt
    obtain ⟨ready,jump,jp,jh,js,jo,jr,jf⟩ :=
      EnumerationSteps.jump_execution program initialized (entry+18) seek
        (by simpa only [Nat.add_assoc,Nat.reduceAdd] using ip) ir (by omega)
        (by simpa [EnumerationDriverCode.jump] using jumpAt 0 (by simp [EnumerationDriverCode.jump]))
        (by simpa [EnumerationDriverCode.jump] using jumpAt 1 (by simp [EnumerationDriverCode.jump]))
    have readyHeap : ready.heap = maskHeap source (∅ : Finset (Fin ands)) := jh.trans (ih.trans readHeap)
    have readyStack : ready.stack = word width ands :: word width 0 :: word width cursor :: state.stack := by
      rw [js,ist,rs]
    obtain ⟨searched,st,sp,searchTrace,searchTime,searchSpace,so,result⟩ :=
      SupportSearchRun.returning_from_state program source query seek call found Q S ands
        (.constant 0 (word width 0)) callback coreAt (by omega) limitFits
        (by rw [heapStored,maskHeap_size,sameSize] at heapFits; exact heapFits)
        (word width cursor :: state.stack) ready jp jr readyHeap readyStack
        ((jf 3 (by decide)).trans ic) (by simpa only [Nat.min_self] using (jf 5 (by decide)).trans ib)
    rw [leaves_saturated _ _ le_rfl] at searchTime
    have readLive : read.liveWords = state.liveWords+1 := by
      simp only [State.liveWords,rh,rs,ro,Array.size_set,List.length_cons]; omega
    have initLive : initialized.liveWords = state.liveWords+3 := by
      have growth : initialized.liveWords = read.liveWords+2 := by
        simp only [State.liveWords,ih,ist,io,List.length_cons]; omega
      omega
    have readyLive : ready.liveWords = state.liveWords+3 := by simp only [State.liveWords,jh,js,jo]; exact initLive
    have outputEq : ready.output = state.output := jo.trans (io.trans ro)
    have spaceBound : sp ≤ source.size+3*ands+S+state.stack.length+state.output.length+12 := by
      simp only [List.length_cons,outputEq] at searchSpace; omega
    have initialTrace := first.append (setup.append jump)
    have prefixTrace : Execution program state ready 20 (state.liveWords+3) := by
      simpa only [readLive,initLive,Nat.max_eq_right (by omega : state.liveWords+1 ≤ state.liveWords+3),
        Nat.max_self] using initialTrace
    cases answer : (search (fun chosen : List (Fin ands) => query chosen.toFinset)
        ands (List.finRange ands) []).result with
    | some value =>
      obtain ⟨heap,⟨saved,stack⟩,pc,active⟩ := (show SupportSearchRun.ReturnedOutcome source query seek found
        (word width cursor :: state.stack) searched (some value) from by simpa only [answer] using result)
      refine ⟨searched,20+st,max (state.liveWords+3) sp,prefixTrace.append searchTrace,
        by omega,by omega,so.trans outputEq,heap,?_,pc,active⟩
      exact ⟨saved++[word width cursor], by simpa only [List.append_assoc,List.singleton_append] using stack⟩
    | none =>
      obtain ⟨heap,stack,pc,active⟩ := (show SupportSearchRun.ReturnedOutcome source query seek found
        (word width cursor :: state.stack) searched none from by simpa only [answer] using result)
      obtain ⟨final,last,fp,fh,fs,fo,fr,_⟩ :=
        EnumerationSteps.jump_execution program searched (SupportTraversal.done seek) rejected pc active
          (by unfold SupportTraversal.done; omega)
          (by simpa [EnumerationDriverCode.jump] using returnAt 0 (by simp [EnumerationDriverCode.jump]))
          (by simpa [EnumerationDriverCode.jump] using returnAt 1 (by simp [EnumerationDriverCode.jump]))
      have live : searched.liveWords = state.liveWords+1 := by
        simp only [State.liveWords,heap,maskHeap_size,stack,List.length_cons,so,outputEq,
          heapStored,sameSize]; omega
      refine ⟨final,20+(st+2),max (state.liveWords+3) (max sp searched.liveWords),
        prefixTrace.append (searchTrace.append last),by omega,by omega,fo.trans (so.trans outputEq),
        fh.trans heap,fs.trans stack,fp,fr⟩

def scan (query : Fin m → Finset (Fin ands) → Option β) (healthy : Fin m → Bool) : List (Fin m) → Option β
  | [] => none
  | root :: rest =>
    match if healthy root then (search (fun chosen : List (Fin ands) => query root chosen.toFinset)
        ands (List.finRange ands) []).result else none with
    | some value => some value
    | none => scan query healthy rest

def driverCode (width loop count rootBase slot healthyBase seek done ands : Nat) : List (Instruction width 8) :=
  (SharedTagCompare.code width done count 3).toList ++
    attemptCode width rootBase slot healthyBase (loop+23) seek ands

@[simp] theorem driverCode_length :
    (driverCode width loop count rootBase slot healthyBase seek done ands).length = 23 := by simp [driverCode]

def SearchOutcome (source : Nat → Array (Word width)) (query : Fin m → Finset (Fin ands) → Option β)
    (healthy : Fin m → Bool) (observations : List (Fin m)) (found done : Nat)
    (rest : List (Word width)) (final : State width 8) : Option β → Prop
  | none => (∃ last, final.heap = maskHeap (source last) (∅ : Finset (Fin ands))) ∧
      final.stack = rest ∧ final.pc = word width done ∧ final.halted = false
  | some value => (∃ root ∈ observations, healthy root = true ∧
      ∃ chosen, final.heap = maskHeap (source root.val) chosen ∧ query root chosen = some value) ∧
      (∃ saved, final.stack = saved ++ rest) ∧ final.pc = word width found ∧ final.halted = false

private theorem mask_prefix (source : Array (Word width)) (chosen : Finset (Fin ands))
    (address : Nat) (value : Word width) (stored : source[address]? = some value) :
    (maskHeap source chosen)[address]? = some value := by
  unfold maskHeap Controller.Cost.ForestInputStored.withValues
  rw [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp stored).1]
  exact stored

set_option maxHeartbeats 2500000 in
theorem execution (program : Program width 8) (source : Nat → Array (Word width))
    (query : Fin m → Finset (Fin ands) → Option β) (healthy : Fin m → Bool)
    (loop count rootBase slot healthyBase seek call found done Q S : Nat)
    (sourceSize : ∀ root, (source root).size = (source 0).size)
    (slotBound : slot < (source 0).size)
    (separate : ∀ root : Fin m, healthyBase+root.val ≠ slot)
    (updates : ∀ before root, (maskHeap (source before) (∅ : Finset (Fin ands))).set slot (word width root)
        (by simp only [maskHeap_size,sourceSize]; omega) = maskHeap (source root) (∅ : Finset (Fin ands)))
    (healthCells : ∀ before (root : Fin m), (source before)[healthyBase+root.val]? = some (boolWord width (healthy root)))
    (callbacks : ∀ root : Fin m, Callback program (source root.val) (query root) seek call found Q S)
    (driverAt : SharedRootRead.BlockAt program loop
      (driverCode width loop count rootBase slot healthyBase seek done ands))
    (advanceAt : SharedRootRead.BlockAt program (loop+23) (advanceCode width loop))
    (coreAt : SharedRootRead.BlockAt program seek
      (SupportTraversal.endingCode width seek ands (source 0).size call (.constant 0 (word width 0))))
    (returnAt : SharedRootRead.BlockAt program (SupportTraversal.done seek) (EnumerationDriverCode.jump width (loop+23)))
    (loopRoom : loop+28 < 2^width) (searchRoom : seek+37 < 2^width)
    (countFits : count < 2^width) (limitFits : ands < 2^width)
    (heapFits : (source 0).size+ands < 2^width)
    (observations : List (Fin m)) (cursor before : Nat) (state : State width 8)
    (total : cursor+observations.length = count)
    (rootCells : ∀ before i (below : i<observations.length),
      (source before)[rootBase+cursor+i]? = some (word width ((observations[i]'below).val)))
    (heapStored : state.heap = maskHeap (source before) (∅ : Finset (Fin ands)))
    (held : state.reg 3 = word width cursor)
    (position : state.pc = word width loop) (running : state.halted = false) :
    ∃ final ticks peak, Execution program state final ticks peak ∧
      ticks ≤ (Q+90)*2^ands*observations.length+3 ∧
      peak ≤ (source 0).size+3*ands+S+state.stack.length+state.output.length+12 ∧
      final.output = state.output ∧
      SearchOutcome source query healthy observations found done state.stack final (scan query healthy observations) := by
  induction observations generalizing cursor before state with
  | nil =>
    have compareAt := block_left program loop _ _ driverAt
    obtain ⟨final,trace,fh,fs,fo,fp,fr,_⟩ :=
      SharedTagCompare.execution program state loop done count cursor 3 (by decide) position running (by omega)
        countFits (by simp only [List.length_nil] at total; omega) held (block_code _ _ _ compareAt)
    have live : state.liveWords = (source 0).size+ands+state.stack.length+state.output.length+9 := by
      simp only [State.liveWords,heapStored,maskHeap_size,sourceSize]; omega
    refine ⟨final,3,state.liveWords,trace,by simp,by omega,fo,⟨before,fh.trans heapStored⟩,fs,?_,fr⟩
    simpa only [List.length_nil,Nat.add_zero] using fp.trans (by rw [ite_eq_left (by simpa using total)])
  | cons root rest ih =>
    have compareAt := block_left program loop _ _ driverAt
    have attemptAt := block_right program loop _ _ driverAt
    simp only [Array.length_toList,SharedTagCompare.code_size] at attemptAt
    have cursorLess : cursor < count := by simp only [List.length_cons] at total; omega
    obtain ⟨tested,compare,ch,cs,co,cp,cr,cf⟩ :=
      SharedTagCompare.execution program state loop done count cursor 3 (by decide) position running (by omega)
        countFits (by omega) held (block_code _ _ _ compareAt)
    have pc : tested.pc = word width (loop+3) := by simpa only [ite_eq_right (by omega : cursor≠count)] using cp
    have currentCell : (source before)[rootBase+cursor]? = some (word width root.val) := by
      have cell := rootCells before 0 (by simp)
      change (source before)[rootBase+cursor+0]? = some (word width root.val) at cell
      simpa only [Nat.add_zero] using cell
    have currentHeap : tested.heap = maskHeap (source before) (∅ : Finset (Fin ands)) := ch.trans heapStored
    obtain ⟨attempted,attemptTicks,ap,attempt,attemptTime,attemptSpace,ao,result⟩ :=
      attempt_execution program tested (source before) (source root.val) (query root)
        (loop+3) rootBase slot healthyBase (loop+23) seek call found cursor root.val Q S (healthy root)
        ((sourceSize before).trans (sourceSize root.val).symm) currentHeap
        (by rw [currentHeap,maskHeap_size,sourceSize]; omega)
        (by simpa only [currentHeap] using updates before root.val)
        (by rw [currentHeap]; exact mask_prefix _ _ _ _ currentCell)
        (by rw [currentHeap]; exact mask_prefix _ _ _ _ (healthCells before root))
        (separate root) ((cf 3 (by decide)).trans held) pc cr (by omega) searchRoom
        (by simpa only [currentHeap,maskHeap_size,sourceSize] using heapFits) limitFits attemptAt (callbacks root)
        (by simpa only [sourceSize] using coreAt) returnAt
    have testedLive : tested.liveWords = state.liveWords := by simp only [State.liveWords,ch,cs,co]
    have startLive : state.liveWords = (source 0).size+ands+state.stack.length+state.output.length+9 := by
      simp only [State.liveWords,heapStored,maskHeap_size,sourceSize]; omega
    have joined := compare.append attempt
    have space : max state.liveWords ap ≤ (source 0).size+3*ands+S+state.stack.length+state.output.length+12 := by
      rw [sourceSize,cs,co] at attemptSpace; omega
    have power : 1 ≤ 2^ands := Nat.one_le_pow _ _ (by decide)
    have oneBudget : 3+attemptTicks+5 ≤ (Q+90)*2^ands := by nlinarith [attemptTime]
    cases answer : (if healthy root then (search (fun chosen : List (Fin ands) => query root chosen.toFinset)
        ands (List.finRange ands) []).result else none) with
    | some value =>
      obtain ⟨heap,⟨saved,stack⟩,fp,fr⟩ := (show Outcome (source root.val) (query root) found (loop+23) cursor
        tested.stack attempted (some value) from by simpa only [answer] using result)
      have healthyTrue : healthy root = true := by cases h : healthy root <;> simp_all
      simp only [scan,answer,SearchOutcome]
      refine ⟨attempted,3+attemptTicks,max state.liveWords ap,joined,?_,space,ao.trans co,?_,
        ⟨saved,by simpa only [cs] using stack⟩,fp,fr⟩
      · simp only [List.length_cons]; nlinarith
      · obtain ⟨chosen,heap,meaning⟩ := heap
        exact ⟨root,by simp,healthyTrue,chosen,heap,meaning⟩
    | none =>
      obtain ⟨ah,ast,apos,ar⟩ := (show Outcome (source root.val) (query root) found (loop+23) cursor
        tested.stack attempted none from by simpa only [answer] using result)
      obtain ⟨advanced,advance,nh,ns,no,np,nr,nc⟩ :=
        advance_execution program attempted (loop+23) loop cursor state.stack apos ar
          (by simpa only [cs] using ast) (by omega) (by omega) advanceAt
      have advancedHeap : advanced.heap = maskHeap (source root.val) (∅ : Finset (Fin ands)) := nh.trans ah
      obtain ⟨final,tt,pp,tailTrace,tailTime,tailSpace,fo,tailResult⟩ :=
        ih (cursor+1) root.val advanced (by simp only [List.length_cons] at total; omega)
          (by intro before i below
              have cell := rootCells before (i+1) (by simp; omega)
              simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cell)
          advancedHeap nc np nr
      have attemptedLive : attempted.liveWords = state.liveWords+1 := by
        simp only [State.liveWords,ah,maskHeap_size,ast,cs,List.length_cons,ao,co,
          heapStored,sourceSize]; omega
      have allSpace : max (max state.liveWords ap) (max attempted.liveWords pp) ≤
          (source 0).size+3*ands+S+state.stack.length+state.output.length+12 := by
        rw [ns,no,ao,co] at tailSpace
        omega
      refine ⟨final,(3+attemptTicks)+(5+tt),max (max state.liveWords ap) (max attempted.liveWords pp),
        joined.append (advance.append tailTrace),?_,allSpace,fo.trans (no.trans (ao.trans co)),?_⟩
      · simp only [List.length_cons,ns,no,ao,co] at tailTime ⊢; nlinarith
      · rw [show scan query healthy (root::rest) = scan query healthy rest by simp only [scan,answer]]
        cases tailAnswer : scan query healthy rest with
        | none =>
          simpa only [scan,answer,tailAnswer,SearchOutcome,ns] using tailResult
        | some value =>
          simp only [SearchOutcome]
          obtain ⟨⟨selected,member,health,chosen,heap,meaning⟩,stack,fp,fr⟩ :=
            (show SearchOutcome source query healthy rest found done advanced.stack final (some value) from
              by simpa only [tailAnswer] using tailResult)
          exact ⟨⟨selected,by simp [member],health,chosen,heap,meaning⟩,
            by simpa only [ns] using stack,fp,fr⟩

end Controller.Extensions.ResolvedRootLoop
