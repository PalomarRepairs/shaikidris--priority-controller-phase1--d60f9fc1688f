module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Extensions.SupportCallback
public import Controller.Extensions.SupportSearchInit
public import Controller.Extensions.ResolvedRootSource

@[expose] public section

/-! The healthy-zero phase allocates its own support mask and sentinel. A
successful candidate branches to the native continuation; exhaustion releases
the mask and returns the retained healthy source to the next phase. -/
namespace Controller.Extensions.SupportSearchBody
open Controller Controller.Decoder Controller.Decoder.DAG Controller.Cost
open Controller.Cost.ForestIndexedOperands Controller.Cost.ForestInputStored
open Controller.Cost.SharedDetectorAssembly

def seek (n : Nat) : Nat := 2*n+6
def call (n : Nat) : Nat := seek n+37
def cleanup (n b : Nat) (roots : List Nat) : Nat := call n+148+15*roots.length+(if b=1 then 11 else 0)

def code (width : Nat) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (healthy : Fin graph.nodeCount → Bool) (k b : Nat) (target : Channel n) (found done : Nat) :
    List (Instruction width 8) :=
  let packet := SupportCandidate.header width n rows roots healthy
  SupportSearchInit.code width n (k+1) ++
    (SupportTraversal.endingCode width (seek n) n (cacheHeap width packet rows roots).size (call n)
      (.constant 0 (word width 0)) ++
    ([.branchZero 0 (word width (cleanup n b roots))] ++
    (SupportCallback.code width n b packet rows roots target.val (call n) found (SupportTraversal.backtrack (seek n)) ++
      (SharedEvaluationReclaim.code width (cleanup n b roots) done n).toList)))

theorem code_length (graph : DAG n) (rows : List Row) (roots : List Nat)
    (healthy : Fin graph.nodeCount → Bool) (k b : Nat) (target : Channel n) (found done : Nat) :
    (code width graph rows roots healthy k b target found done).length =
    cleanup n b roots+7 := by
  simp only [code,List.length_append,SupportSearchInit.code_length,SupportTraversal.endingCode_length,
    List.length_cons,List.length_nil,SupportCallback.code_length,Array.length_toList,
    SharedEvaluationReclaim.code_size,cleanup,call,seek]
  omega

theorem healthy_independent (graph : DAG n) (rows : List Row) (roots : List Nat)
    (left right : Fin graph.nodeCount → Bool) (k b : Nat) (target : Channel n) (found done : Nat) :
    code width graph rows roots left k b target found done = code width graph rows roots right k b target found done := by
  have kernel := SupportSourceRound.kernel_header_independent (width := width) (n := n) rows roots
    (SupportCandidate.header width n rows roots left) (SupportCandidate.header width n rows roots right) (by simp)
  simp only [code,SupportCallback.code,SupportCandidate.code,SupportSourceRound.code,kernel,
    SupportCandidate.header_size,cacheHeap_size,UniformDAGRuntimeOutputs.rootBase]

def Outcome (source : Array (Word width)) (query : Finset (Channel n) → Option β)
    (found done : Nat) (rest : List (Word width)) (final : State width 8) : Option β → Prop
  | none => final.heap = source ∧ final.stack = rest ∧ final.pc = word width done ∧ final.halted = false
  | some value => SupportSearchRun.Outcome source query found rest final (some value)

set_option maxHeartbeats 2000000 in
theorem execution (resident : Program width 8) (graph : DAG n) (rows : List Row) (roots : List Nat)
    (matched : RowsMatch graph rows) (heads : UniformDAGSource.HeadsMatch graph rows matched)
    (rootMatches : RootsMatch graph roots) (healthy : Fin graph.nodeCount → Bool)
    (k b : Nat) (target : Channel n) (found done : Nat) (state : State width 8)
    (heapStored : state.heap = cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots)
    (position : state.pc = word width 0) (running : state.halted = false)
    (capacity : 4096*(graph.countedSize+1)<2^width)
    (present : SharedRootRead.BlockAt resident 0 (code width graph rows roots healthy k b target found done)) :
    ∃ final ticks peak, Execution resident state final ticks peak ∧
      ticks ≤ (100*(graph.countedSize+1)+50)*BoundedAnd.supportCount n k+100*(graph.countedSize+1) ∧
      peak ≤ 100*(graph.countedSize+1)+state.stack.length+state.output.length ∧ final.output = state.output ∧
      Outcome (cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots)
        (BoundedAnd.supportQuery graph b target healthy) found done state.stack final
        (SupportStream.scanSupports graph k b target healthy) := by
  let source := cacheHeap width (SupportCandidate.header width n rows roots healthy) rows roots
  have size := graph.countedSize_eq
  have rootCount : roots.length = graph.roots.length := by rw [rootMatches]; simp
  have retainedBound := ResolvedRootSource.source_bound (width := width) graph healthy 0 matched rootMatches
  have sourceBound : source.size ≤ 40*(graph.countedSize+1) := by
    simpa only [source,ResolvedRootSource.source,cacheHeap_size,ResolvedRootSource.packet_size,
      SupportCandidate.header_size] using le_trans (Nat.le_add_right _ _) retainedBound
  have codeAt := present
  unfold code at codeAt
  have initAt := block_left resident 0 _ _ codeAt
  have afterInit := block_right resident 0 _ _ codeAt
  simp only [SupportSearchInit.code_length,Nat.zero_add] at afterInit
  have coreAt := block_left resident (seek n) _ _ afterInit
  have afterCore := block_right resident (seek n) _ _ afterInit
  simp only [SupportTraversal.endingCode_length] at afterCore
  have jumpAt := block_left resident (seek n+36) _ _ afterCore
  have afterJump := block_right resident (seek n+36) _ _ afterCore
  simp only [List.length_singleton] at afterJump
  have callbackAt := block_left resident (call n) _ _ afterJump
  have releaseAt := block_right resident (call n) _ _ afterJump
  simp only [SupportCallback.code_length] at releaseAt
  obtain ⟨initialized,init,ih,is,io,ip,ir,ic,ib⟩ :=
    SupportSearchInit.execution resident state 0 n (k+1) position running (by omega)
      (by rw [heapStored]; change source.size+n < 2^width; omega) initAt
  have callback := SupportCallback.contract resident graph rows roots matched heads rootMatches healthy target b
    (seek n) (call n) found (by dsimp only [seek,call]; omega)
    (by change source.size+n+graph.nodeCount < 2^width; omega) callbackAt
  obtain ⟨searched,st,sp,search,stime,sspace,out,result⟩ :=
    SupportSearchRun.returning_from_state resident source (BoundedAnd.supportQuery graph b target healthy)
      (seek n) (call n) found (100*(graph.countedSize+1)) (graph.nodeCount+5) (k+1)
      (.constant 0 (word width 0)) callback coreAt (by dsimp only [seek]; omega)
      (by omega) (by omega) state.stack initialized (by simpa [seek] using ip) ir
      (by simpa only [heapStored] using ih) is ic ib
  rw [SupportStream.leaves_eq_supportCount] at stime
  change SupportSearchRun.ReturnedOutcome _ _ (seek n) found state.stack searched
    (SupportStream.scanSupports graph k b target healthy) at result
  have initialLive : state.liveWords ≤ 40*(graph.countedSize+1)+state.stack.length+state.output.length+9 := by
    simp only [State.liveWords]
    change 8+state.heap.size+state.stack.length+state.output.length+1 ≤ _
    rw [heapStored]
    change 8+source.size+state.stack.length+state.output.length+1 ≤ _
    omega
  have searchedLive : searched.liveWords ≤ sp := search.final_storage_le
  rw [io] at sspace out
  cases answer : SupportStream.scanSupports graph k b target healthy with
  | some K =>
    refine ⟨searched,2*n+6+st,max (state.liveWords+n+2) sp,init.append search,by omega,by omega,
      out,?_⟩
    simpa only [answer,Outcome,SupportSearchRun.ReturnedOutcome] using result
  | none =>
    rw [answer] at result
    obtain ⟨sh,ss,pc,active⟩ := result
    have endAt := (SupportTraversal.ending_blocks resident (seek n) n source.size (call n)
      (.constant 0 (word width 0)) coreAt).2.2.2.2
    obtain ⟨jumped,jump,jp,jh,js,jo,jr,_⟩ :=
      EnumerationSteps.jump_execution resident searched (SupportTraversal.done (seek n)) (cleanup n b roots)
        pc active (by dsimp only [SupportTraversal.done,seek]; omega) endAt
        (by simpa only [SupportTraversal.done,Nat.add_assoc,Nat.reduceAdd,Nat.add_zero,List.getElem?_cons_zero]
          using jumpAt 0 (by simp))
    let values := List.replicate n (word width 0)
    have zeroHeap : jumped.heap = source ++ values.toArray := by
      rw [jh,sh]
      simp [SupportSearch.maskHeap,withValues,values,boolWord,List.ofFn_const]
    obtain ⟨final,release,fh,fs,fo,fp,fr,_⟩ :=
      SharedGraphReclaim.setup_execution resident jumped (cleanup n b roots) done source values jp jr
        (by dsimp only [cleanup,call,seek]; split <;> omega) zeroHeap (by simp [values]; omega)
        (by simpa only [values,List.length_replicate,cleanup,Nat.add_assoc] using block_code _ _ _ releaseAt)
    have jumpLive : jumped.liveWords = searched.liveWords := by simp only [State.liveWords,jh,js,jo]
    refine ⟨final,2*n+6+(st+(2+(4*values.length+4))),
      max (state.liveWords+n+2) (max sp (max searched.liveWords jumped.liveWords)),
      init.append (search.append (jump.append release)),by simp only [values,List.length_replicate]; omega,
      by rw [jumpLive]; omega,fo.trans (jo.trans out),?_⟩
    simpa only [Outcome,answer] using And.intro fh (And.intro (fs.trans (js.trans ss)) (And.intro fp fr))

end Controller.Extensions.SupportSearchBody
