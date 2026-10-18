module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedQueryCleanupCode

@[expose] public section

namespace Controller.Cost.SharedQueryTailCode
open Controller.Cost.GateProgram Controller.Native Controller.Native.SourceController

abbrev projection (entry : Nat) := entry + 134

def cleanup (parameters : Parameters) (width nativeBase entry : Nat) : Nat :=
  projection entry +
    (NativeRetainedExecution.code parameters width nativeBase
      (SharedNativeSuccessCode.nativeEntry (projection entry))).length +
    3 * (compile parameters).toState.count + 65

def success (parameters : Parameters) (width nativeBase entry : Nat) : List (Instruction width 8) :=
  SharedNativeSuccessCode.code parameters width nativeBase (projection entry)
    (cleanup parameters width nativeBase entry + 7)

@[simp] theorem success_length : (success parameters width nativeBase entry).length =
    cleanup parameters width nativeBase entry - projection entry := by
  simp only [success, SharedNativeSuccessCode.code_length, cleanup]
  omega

@[irreducible] def code (parameters : Parameters) (width entry n base nativeBase : Nat) : List (Instruction width 8) :=
  (SharedWorklistCode.code width entry n base (projection entry)
    (cleanup parameters width nativeBase entry)).toList ++
  success parameters width nativeBase entry ++
  SharedQueryCleanupCode.code width (cleanup parameters width nativeBase entry)

structure Physical (parameters : Parameters) (program : Program width 8)
    (entry n base nativeBase : Nat) : Prop where
  worklist : SharedWorklistCode.Physical program entry n base (projection entry)
    (cleanup parameters width nativeBase entry)
  success : SharedRootRead.BlockAt program (projection entry)
    (SharedNativeSuccessCode.code parameters width nativeBase (projection entry)
      (cleanup parameters width nativeBase entry + 7))
  cleanup : SharedQueryCleanupCode.Physical program (cleanup parameters width nativeBase entry)

set_option maxHeartbeats 2000000 in
theorem physical_at (parameters : Parameters) (program : Program width 8)
    (entry n base nativeBase : Nat)
    (present : SharedRootRead.BlockAt program entry (code parameters width entry n base nativeBase)) :
    Physical parameters program entry n base nativeBase := by
  unfold code at present
  have worklist : SharedRootRead.BlockAt program entry
      (SharedWorklistCode.code width entry n base (projection entry)
        (cleanup parameters width nativeBase entry)).toList := by
    intro offset bound
    have found := present offset (by
      simp only [List.length_append]
      omega)
    rw [List.getElem?_append_left (by
      simp only [List.length_append]
      omega), List.getElem?_append_left bound] at found
    exact found
  have native := SharedNativeSuccessCode.segment program entry _ _ _ present
  simp only [Array.length_toList, SharedWorklistCode.code_size] at native
  have prepared : SharedRootRead.BlockAt program entry
      (((SharedWorklistCode.code width entry n base (projection entry)
        (cleanup parameters width nativeBase entry)).toList ++
        success parameters width nativeBase entry) ++
        SharedQueryCleanupCode.code width (cleanup parameters width nativeBase entry) ++ []) := by
    simpa only [List.append_assoc, List.append_nil] using present
  have released := SharedNativeSuccessCode.segment program entry _ _ _ prepared
  have address : entry +
      ((SharedWorklistCode.code width entry n base (projection entry)
        (cleanup parameters width nativeBase entry)).toList ++
        success parameters width nativeBase entry).length =
      cleanup parameters width nativeBase entry := by
    simp only [List.length_append, Array.length_toList, SharedWorklistCode.code_size,
      success, SharedNativeSuccessCode.code_length, cleanup, projection]
    omega
  rw [address] at released
  exact ⟨SharedWorklistCode.physical_at program entry n base _ _ worklist,
    native, SharedQueryCleanupCode.physical_at program _ released⟩

end Controller.Cost.SharedQueryTailCode
