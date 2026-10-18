module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationDriverDescent

@[expose] public section

/-! The local initialization, descent and sibling-query blocks are physically
present in the already constructed immutable seventeen-block driver. -/
namespace Controller.Cost.EnumerationDriverControlAt
open Controller.Decoder Controller.Native Controller.Cost.GateProgram
open Controller.Cost.EnumerationDriverCode Controller.Cost.EnumerationDriverLayout

theorem initial (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (code parameters graph width entry rows roots)) :
    SharedRootRead.BlockAt program entry
      (EnumerationDriverInitial.code width parameters.drive (initWords parameters width)
        (labels parameters graph width entry).call (labels parameters graph width entry).halt) := by
  have found := physical parameters graph width entry rows roots program present 0 (by decide)
  simpa [entries, chunks, EnumerationDriverInitial.code, EnumerationDriverControl.modeCode, labels, List.append_assoc] using found

theorem descent (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (code parameters graph width entry rows roots)) :
    SharedRootRead.BlockAt program (labels parameters graph width entry).descend
      (EnumerationDriverDescent.freeCode parameters width (SharedDetectorPrepared.packetSize graph)
        (labels parameters graph width entry).emit (labels parameters graph width entry).forcedDescend (labels parameters graph width entry).call) := by
  have found := physical parameters graph width entry rows roots program present 9 (by decide)
  simpa [entries, chunks, EnumerationDriverDescent.freeCode, EnumerationDriverDescent.checks,
    EnumerationDriverControl.selectCode, EnumerationDriverControl.modeCode, List.append_assoc] using found

theorem forced_descent (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (code parameters graph width entry rows roots)) :
    SharedRootRead.BlockAt program (labels parameters graph width entry).forcedDescend
      (EnumerationDriverControl.incrementCode width (labels parameters graph width entry).descend) := by
  have found := physical parameters graph width entry rows roots program present 10 (by decide)
  simpa only [entries, chunks, List.getElem_cons_succ, List.getElem_cons_zero, EnumerationDriverControl.incrementCode] using found

theorem sibling (parameters : Parameters) (graph : DAG parameters.channels) (width entry : Nat)
    (rows : List ForestIndexedOperands.Row) (roots : List Nat) (program : Program width 8)
    (present : SharedRootRead.BlockAt program entry (code parameters graph width entry rows roots)) :
    SharedRootRead.BlockAt program (labels parameters graph width entry).seekTry
      (EnumerationDriverControl.pairModeCode width (SharedDetectorPrepared.packetSize graph)
        (SharedDetectorPrepared.packetSize graph + parameters.channels) true false 2 (labels parameters graph width entry).call) := by
  have found := physical parameters graph width entry rows roots program present 13 (by decide)
  simpa [entries, chunks, EnumerationDriverControl.pairModeCode, EnumerationDriverControl.pairCode,
    EnumerationDriverControl.modeCode, List.append_assoc] using found

end Controller.Cost.EnumerationDriverControlAt
