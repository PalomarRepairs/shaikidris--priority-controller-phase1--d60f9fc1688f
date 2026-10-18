module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedNormalizerCode

public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Controller.Cost.SharedSolverPrefix
open Controller.Cost.GateProgram Controller.Cost.ForestZeroAdmissibleCaller

def code (width entry n base directoryHeader endHeader inputHeader firstHeader recordHeader scan : Nat) : Program width 8 :=
  scratchCountCode width ++ Controller.Horn.TrackedAllocate.code width (entry + 11) ++
  scratchHeaderCode width ++ scratchEndpointCode (width := width) ++ saveProjectionCode (width := width) ++
  SharedNormalizerCode.code width (entry + 42) n base directoryHeader endHeader inputHeader firstHeader recordHeader ++
  ForestZeroHeaderBridge.saveCode width recordHeader ++ Controller.Horn.IndexScan.code (n := n) width base (base + 5 * n + 4) (entry + 210) ++
  ForestZeroHeaderBridge.restoreCode width ++ ForestZeroReclaim.captureCode width ++
  ForestZeroSeedSetup.code (n := n) width base recordHeader (base + 5 * n + 4) scan

@[simp] theorem code_size :
    (code width entry n base directoryHeader endHeader inputHeader firstHeader recordHeader scan).size = 261 := by
  simp [code, scratchCountCode, scratchHeaderCode, scratchEndpointCode, saveProjectionCode,
    ForestZeroHeaderBridge.saveCode, ForestZeroHeaderBridge.restoreCode, ForestZeroReclaim.captureCode,
    ForestZeroSeedSetup.code, Controller.Horn.TrackedAllocate.code, Controller.Horn.IndexScan.code]

theorem normalizer_at (program : Program width 8) (entry scan : Nat)
    (clauses : List (Controller.CNF.Clause (Fin n))) (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : SharedRootRead.BlockAt program entry
      (code width entry n layout.base layout.directoryHeader layout.endHeader layout.inputHeader layout.firstHeader layout.recordHeader scan).toList) :
    Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) clauses layout := by
  apply SharedNormalizerCode.resident_at
  intro offset bound
  have offsetBound : offset < 161 := by simpa using bound
  have found := present (42 + offset) (by simp at bound ⊢; omega)
  simp only [Array.getElem?_toList] at found ⊢
  rw [show (entry + 42) + offset = entry + (42 + offset) by omega]
  rw [found]
  simp [code, Array.getElem?_append, Array.size_append, SharedNormalizerCode.code_size,
    Controller.Horn.IndexScan.code_size, Controller.Horn.TrackedAllocate.code_size,
    scratchCountCode, scratchHeaderCode, scratchEndpointCode, saveProjectionCode,
    ForestZeroHeaderBridge.saveCode, ForestZeroHeaderBridge.restoreCode, ForestZeroReclaim.captureCode,
    ForestZeroSeedSetup.code, List.length_cons, List.length_nil]
  split_ifs <;> simp_all <;> first | omega | congr 1 <;> omega


structure Physical (program : Program width 8) (entry n base recordHeader scan : Nat) : Prop where
  count : ∀ phase : Fin 11, program[entry + phase.val]? = (scratchCountCode width)[phase.val]?
  allocate : Controller.Horn.TrackedAllocate.CodeAt program (entry + 11)
  headers : ∀ phase : Fin 15, program[entry + 16 + phase.val]? = (scratchHeaderCode width)[phase.val]?
  endpoint : ∀ phase : Fin 5, program[entry + 31 + phase.val]? = (scratchEndpointCode (width := width))[phase.val]?
  saved : ∀ phase : Fin 6, program[entry + 36 + phase.val]? = (saveProjectionCode (width := width))[phase.val]?
  indexSave : ForestZeroHeaderBridge.SaveAt program (entry + 203) recordHeader
  index : Controller.Horn.IndexScan.At (n := n) program (entry + 210) base (base + 5 * n + 4)
  indexRestore : ForestZeroHeaderBridge.RestoreAt program (entry + 242)
  capture : ∀ phase : Fin 6, program[entry + 245 + phase.val]? = (ForestZeroReclaim.captureCode width)[phase.val]?
  seed : ∀ phase : Fin 10, program[entry + 251 + phase.val]? =
    (ForestZeroSeedSetup.code (n := n) width base recordHeader (base + 5 * n + 4) scan)[phase.val]?

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem physical_at (program : Program width 8) (entry n base directoryHeader endHeader inputHeader firstHeader recordHeader scan : Nat)
    (present : SharedRootRead.BlockAt program entry
      (code width entry n base directoryHeader endHeader inputHeader firstHeader recordHeader scan).toList) :
    Physical program entry n base recordHeader scan := by
  have fetched : ∀ offset, offset < 261 → program[entry + offset]? =
      (code width entry n base directoryHeader endHeader inputHeader firstHeader recordHeader scan)[offset]? := by
    intro offset bound
    simpa only [Array.getElem?_toList] using present offset (by simp; exact bound)
  constructor
  all_goals intro phase
  all_goals fin_cases phase
  all_goals try simp only [Nat.add_assoc, Nat.reduceAdd]
  all_goals rw [fetched _ (by omega)]
  all_goals simp [code, Array.getElem?_append, scratchCountCode, scratchHeaderCode, scratchEndpointCode, saveProjectionCode,
    ForestZeroHeaderBridge.saveCode, ForestZeroHeaderBridge.restoreCode, ForestZeroReclaim.captureCode,
    ForestZeroSeedSetup.code, Controller.Horn.WorklistSeed.setupCode,
    Controller.Horn.TrackedAllocate.code, Controller.Horn.IndexScan.code, Controller.Horn.IndexScan.setupPrefix, Controller.Horn.IndexScan.suffix,
    Controller.Horn.IndexBuild.code, Nat.add_assoc]


theorem root_code_irrel (graph : Controller.Decoder.DAG n) (b : Nat) (target : Fin n)
    (T F : Finset (Fin n)) (left right : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : Controller.Cost.ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size)
    (entry scan : Nat) :
    code width entry
      (constructorDictionary heap layout (Controller.Cost.ForestZeroCompile.empty _)
        (SharedZeroSource.references graph b target T F base slot left)).coordinates.size
      (constructorHeap heap layout (Controller.Cost.ForestZeroCompile.empty _)
        (SharedZeroSource.references graph b target T F base slot left) n).size
      (heap.size + 3) (heap.size + 4) (heap.size + 1) (heap.size + 2) heap.size scan =
    code width entry
      (constructorDictionary heap layout (Controller.Cost.ForestZeroCompile.empty _)
        (SharedZeroSource.references graph b target T F base slot right)).coordinates.size
      (constructorHeap heap layout (Controller.Cost.ForestZeroCompile.empty _)
        (SharedZeroSource.references graph b target T F base slot right) n).size
      (heap.size + 3) (heap.size + 4) (heap.size + 1) (heap.size + 2) heap.size scan := by
  rw [SharedZeroSource.dictionary_size, SharedZeroSource.dictionary_size,
    SharedZeroSource.constructor_heap_size_root_irrel graph b target T F left right heap layout]

end Controller.Cost.SharedSolverPrefix
