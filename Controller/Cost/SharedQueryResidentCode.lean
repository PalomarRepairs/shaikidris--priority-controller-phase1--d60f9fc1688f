module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedQuerySourceCode

@[expose] public section

namespace Controller.Cost.SharedQueryResidentCode
open Controller.Cost.GateProgram Controller.Cost.ForestZeroEmit
open Controller.Native Controller.Native.SourceController

@[irreducible] def code (parameters : Parameters)
    (width entry keep n base nativeBase : Nat) (references : List (List (Reference ambient))) :
    List (Instruction width 8) :=
  SharedQuerySourceCode.code width entry keep references ++
  SharedQuerySolverCode.code parameters width (SharedQuerySourceCode.solverEntry width entry keep references)
    n base nativeBase (keep + 3) (keep + 4) (keep + 1) (keep + 2) keep

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem code_end (parameters : Parameters) (width entry keep n base nativeBase : Nat)
    (references : List (List (Reference ambient))) :
    entry + (code parameters width entry keep n base nativeBase references).length =
      SharedQueryTailCode.cleanup parameters width nativeBase
        (SharedQuerySourceCode.solverEntry width entry keep references + 261) + 35 := by
  rw [code]
  rw [List.length_append]
  rw [SharedQuerySourceCode.code_length]
  unfold SharedQuerySolverCode.code
  rw [List.length_append, Array.length_toList, SharedSolverPrefix.code_size]
  unfold SharedQueryTailCode.code
  rw [List.length_append, List.length_append, Array.length_toList,
    SharedWorklistCode.code_size, SharedQueryTailCode.success_length,
    SharedQueryCleanupCode.code_length]
  have sourceBefore : entry ≤ SharedQuerySourceCode.solverEntry width entry keep references := by
    unfold SharedQuerySourceCode.solverEntry
    omega
  have projectionBefore : SharedQueryTailCode.projection
      (SharedQuerySourceCode.solverEntry width entry keep references + 261) ≤
      SharedQueryTailCode.cleanup parameters width nativeBase
        (SharedQuerySourceCode.solverEntry width entry keep references + 261) := by
    unfold SharedQueryTailCode.cleanup
    omega
  simp only [SharedQueryTailCode.projection] at projectionBefore ⊢
  omega

structure Physical (parameters : Parameters) (program : Program width 8)
    (entry keep n base nativeBase : Nat) (references : List (List (Reference ambient))) : Prop where
  source : SharedQuerySourceCode.Physical program entry keep references
  solver : SharedQuerySolverCode.Physical parameters program
    (SharedQuerySourceCode.solverEntry width entry keep references) n base nativeBase keep

theorem blocks_at (parameters : Parameters) (program : Program width 8)
    (entry keep n base nativeBase : Nat) (references : List (List (Reference ambient)))
    (present : SharedRootRead.BlockAt program entry
      (code parameters width entry keep n base nativeBase references)) :
    SharedRootRead.BlockAt program entry (SharedQuerySourceCode.code width entry keep references) ∧
    SharedRootRead.BlockAt program (SharedQuerySourceCode.solverEntry width entry keep references)
      (SharedQuerySolverCode.code parameters width (SharedQuerySourceCode.solverEntry width entry keep references)
        n base nativeBase (keep + 3) (keep + 4) (keep + 1) (keep + 2) keep) := by
  unfold code at present
  constructor
  · intro offset bound
    have found := present offset (by simp only [List.length_append]; omega)
    rw [List.getElem?_append_left bound] at found
    exact found
  · have prepared : SharedRootRead.BlockAt program entry
        (SharedQuerySourceCode.code width entry keep references ++
          SharedQuerySolverCode.code parameters width (SharedQuerySourceCode.solverEntry width entry keep references)
            n base nativeBase (keep + 3) (keep + 4) (keep + 1) (keep + 2) keep ++ []) := by
      simpa only [List.append_nil] using present
    have found := SharedNativeSuccessCode.segment program entry _ _ _ prepared
    have address : entry + (SharedQuerySourceCode.code width entry keep references).length =
        SharedQuerySourceCode.solverEntry width entry keep references := by
      rw [SharedQuerySourceCode.code_length]
      unfold SharedQuerySourceCode.solverEntry
      omega
    rw [address] at found
    exact found

theorem physical_at (parameters : Parameters) (program : Program width 8)
    (entry keep n base nativeBase : Nat) (references : List (List (Reference ambient)))
    (present : SharedRootRead.BlockAt program entry
      (code parameters width entry keep n base nativeBase references)) :
    Physical parameters program entry keep n base nativeBase references := by
  obtain ⟨sourceBlock, solverBlock⟩ := blocks_at parameters program entry keep n base nativeBase references present
  exact ⟨SharedQuerySourceCode.physical_at program entry keep references sourceBlock,
    SharedQuerySolverCode.physical_at parameters program
      (SharedQuerySourceCode.solverEntry width entry keep references) n base nativeBase
      (keep + 3) (keep + 4) (keep + 1) (keep + 2) keep solverBlock⟩

theorem root_code_irrel (parameters : Parameters) (graph : Controller.Decoder.DAG n)
    (b : Nat) (target : Fin n) (T F : Finset (Fin n))
    (entry keep localCount base nativeBase coordinateBase slot : Nat)
    (left right : Fin graph.nodeCount) :
    code parameters width entry keep localCount base nativeBase
      (SharedZeroSource.references graph b target T F coordinateBase slot left) =
    code parameters width entry keep localCount base nativeBase
      (SharedZeroSource.references graph b target T F coordinateBase slot right) := by
  unfold code
  rw [SharedQuerySourceCode.root_code_irrel graph b target T F coordinateBase slot entry keep left right,
    SharedQuerySourceCode.root_entry_irrel graph b target T F coordinateBase slot entry keep left right]

end Controller.Cost.SharedQueryResidentCode
