module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.Check

@[expose] public section

/-! Checked dispatch to the original guarded decoder family. The complete
native projection checker also supports live-AND decoders; this additional
syntax check is required before invoking the guarded polynomial algorithm. -/
namespace Controller.Recognition.GuardedFamily
open Controller.Decoder Controller.CNF

def guardedCheck (graph : DAG n) : Bool :=
  (List.finRange graph.nodeCount).all fun i => !(graph.node i).isLiveAnd

theorem guardedCheck_iff (graph : DAG n) : guardedCheck graph = true ↔ graph.Guarded := by
  simp [guardedCheck, DAG.Guarded, Gate.IsGuarded]

def decodeChecked
    (payload : PrivateFamily.CompletePayload source recovered parameters boundary auxCount) :
    Option (PrivateFamily.Record source recovered parameters boundary auxCount) :=
  if guardedCheck parameters.decoder then payload.decodeChecked else none

theorem decodeChecked_sound
    (payload : PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (record : PrivateFamily.Record source recovered parameters boundary auxCount)
    (accepted : decodeChecked payload = some record) :
    parameters.decoder.Guarded ∧ record.check = true ∧
      (Satisfiable source ↔ Physical.BridgeDetectable (b := parameters.buses)
        parameters.bridge parameters.drive parameters.observations) := by
  unfold decodeChecked at accepted
  split at accepted
  next guarded =>
    exact ⟨(guardedCheck_iff parameters.decoder).mp guarded,
      PrivateFamily.CompletePayload.decodeChecked_accepts accepted,
      PrivateFamily.CompletePayload.decodeChecked_projection accepted⟩
  next rejected => simp at accepted

theorem decodeChecked_lifting
    (payload : PrivateFamily.CompletePayload source recovered parameters boundary auxCount)
    (record : PrivateFamily.Record source recovered parameters boundary auxCount)
    (accepted : decodeChecked payload = some record)
    (assignment : Native.Variable parameters → Bool)
    (model : Satisfies assignment parameters.specificationFormula) :
    Satisfies (record.liftNative assignment) source :=
  record.checked_lift_native (decodeChecked_sound payload record accepted).2.1 assignment model

theorem rejects_liveAnd (graph : DAG n) (index : Fin graph.nodeCount)
    (live : (graph.node index).isLiveAnd = true) : guardedCheck graph = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have guarded := (guardedCheck_iff graph).mp accepted index
  simp [Gate.IsGuarded, live] at guarded

end Controller.Recognition.GuardedFamily
