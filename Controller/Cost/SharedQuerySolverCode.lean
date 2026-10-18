module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedQueryTailCode

@[expose] public section

namespace Controller.Cost.SharedQuerySolverCode
open Controller.Cost.GateProgram Controller.Native Controller.Native.SourceController

@[irreducible] def code (parameters : Parameters)
    (width entry n base nativeBase directoryHeader endHeader inputHeader firstHeader recordHeader : Nat) :
    List (Instruction width 8) :=
  (SharedSolverPrefix.code width entry n base directoryHeader endHeader inputHeader firstHeader
    recordHeader (entry + 261)).toList ++
  SharedQueryTailCode.code parameters width (entry + 261) n base nativeBase

structure Physical (parameters : Parameters) (program : Program width 8)
    (entry n base nativeBase recordHeader : Nat) : Prop where
  prepared : SharedSolverPrefix.Physical program entry n base recordHeader (entry + 261)
  tail : SharedQueryTailCode.Physical parameters program (entry + 261) n base nativeBase

theorem blocks_at (parameters : Parameters) (program : Program width 8)
    (entry n base nativeBase directoryHeader endHeader inputHeader firstHeader recordHeader : Nat)
    (present : SharedRootRead.BlockAt program entry
      (code parameters width entry n base nativeBase directoryHeader endHeader inputHeader firstHeader recordHeader)) :
    SharedRootRead.BlockAt program entry
      (SharedSolverPrefix.code width entry n base directoryHeader endHeader inputHeader firstHeader
        recordHeader (entry + 261)).toList ∧
    SharedRootRead.BlockAt program (entry + 261)
      (SharedQueryTailCode.code parameters width (entry + 261) n base nativeBase) := by
  unfold code at present
  constructor
  · intro offset bound
    have found := present offset (by simp only [List.length_append]; omega)
    rw [List.getElem?_append_left bound] at found
    exact found
  · have prepared : SharedRootRead.BlockAt program entry
        ((SharedSolverPrefix.code width entry n base directoryHeader endHeader inputHeader firstHeader
          recordHeader (entry + 261)).toList ++
          SharedQueryTailCode.code parameters width (entry + 261) n base nativeBase ++ []) := by
      simpa only [List.append_nil] using present
    have found := SharedNativeSuccessCode.segment program entry _ _ _ prepared
    simpa only [Array.length_toList, SharedSolverPrefix.code_size] using found

theorem physical_at (parameters : Parameters) (program : Program width 8)
    (entry n base nativeBase directoryHeader endHeader inputHeader firstHeader recordHeader : Nat)
    (present : SharedRootRead.BlockAt program entry
      (code parameters width entry n base nativeBase directoryHeader endHeader inputHeader firstHeader recordHeader)) :
    Physical parameters program entry n base nativeBase recordHeader := by
  obtain ⟨prepared, tail⟩ := blocks_at parameters program entry n base nativeBase
    directoryHeader endHeader inputHeader firstHeader recordHeader present
  exact ⟨SharedSolverPrefix.physical_at program entry n base directoryHeader endHeader inputHeader
    firstHeader recordHeader (entry + 261) prepared,
    SharedQueryTailCode.physical_at parameters program (entry + 261) n base nativeBase tail⟩

theorem normalizer_at (parameters : Parameters) (program : Program width 8)
    (entry nativeBase : Nat) (clauses : List (Controller.CNF.Clause (Fin n)))
    (layout : Controller.Horn.SourceDirectory.Layout clauses)
    (present : SharedRootRead.BlockAt program entry
      (code parameters width entry n layout.base nativeBase layout.directoryHeader layout.endHeader
        layout.inputHeader layout.firstHeader layout.recordHeader)) :
    Controller.Horn.NormalizeLoop.CodeAt program (entry + 42) clauses layout := by
  have prepared := (blocks_at parameters program entry n layout.base nativeBase layout.directoryHeader
    layout.endHeader layout.inputHeader layout.firstHeader layout.recordHeader present).1
  exact SharedSolverPrefix.normalizer_at program entry (entry + 261) clauses layout prepared

end Controller.Cost.SharedQuerySolverCode
