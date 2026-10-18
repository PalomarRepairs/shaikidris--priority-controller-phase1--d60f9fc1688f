module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroChecked

@[expose] public section

/-! The emitted channel prefix decodes to the channel set of this query's actual terminal model. -/
namespace Controller.Cost.SharedZeroOutput
open Controller.CNF Controller.Decoder Controller.Decoder.DAG
open Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroAdmissibleCaller

theorem queue_lift (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (queue : List (Fin dictionary.coordinates.size)) :
    ForestZeroModelLift.lift dictionary true (ForestZeroChannelEmit.localValues queue) =
      ForestZeroModelLift.lift dictionary true (extendNat (Controller.Horn.WorklistOutcome.offAssignment queue)) := by
  funext coordinate
  by_cases unseen : dictionary.slots[coordinate.val] = 0
  · simp [ForestZeroModelLift.lift, unseen]
  · have encoded : dictionary.slots[coordinate.val] = (dictionary.slots[coordinate.val] - 1) + 1 := by omega
    have present := (coherent coordinate _).mp encoded
    have valid := (Array.getElem?_eq_some_iff.mp present).choose
    simp [ForestZeroModelLift.lift, unseen, ForestZeroChannelEmit.localValues, extendNat, valid]

def decode (observed : List (Word width)) (channels : Nat) : Finset (Fin channels) :=
  setOfAssignment (fun channel => decide (observed[channel.val]? = some (word width 1)))

theorem decode_prefix (assignment : Fin channels → Bool) (previous : List (Word width))
    (fits : 1 < 2 ^ width) :
    decode ((List.finRange channels).map (fun channel => ForestZeroChannelEmit.bitWord width (assignment channel)) ++ previous)
      channels = setOfAssignment assignment := by
  have different : word width 0 ≠ word width 1 := by
    intro same
    have values := congrArg Fin.val same
    simp [word, Nat.mod_eq_of_lt fits] at values
  unfold decode
  congr 1
  funext channel
  simp only [List.getElem?_append, List.length_map, List.length_finRange,
    ite_eq_left channel.isLt, List.getElem?_map, Option.map_some]
  cases active : assignment channel <;> simp [ForestZeroChannelEmit.bitWord, active, different]

theorem finite_model_projection (graph : DAG n) (guarded : graph.Guarded) (b : Nat) (target : Fin n)
    (T F : Finset (Fin n)) (root : Fin graph.nodeCount) (assignment : Fin (n + graph.nodeCount) → Bool)
    (model : Satisfies assignment (graph.finiteZeroSystem b target root T F)) :
    Admissible b target (graph.zeroChannelSet (assignment ∘ graph.zeroIndex)) ∧
      ExtendsFixed T F (graph.zeroChannelSet (assignment ∘ graph.zeroIndex)) ∧
      graph.eval (assignmentOfSet (graph.zeroChannelSet (assignment ∘ graph.zeroIndex))) root = false := by
  have source := (satisfies_relabel graph.zeroIndex assignment (graph.zeroSystem b target root T F)).mp model
  apply (graph.zeroSystem_projection guarded b target root T F _).mp
  refine ⟨fun index => (assignment ∘ graph.zeroIndex) (.inr index), ?_⟩
  simpa only [graph.zeroAssignment_channelSet (assignment ∘ graph.zeroIndex)] using source

theorem decoded_witness (graph : DAG n) (guarded : graph.Guarded) (b : Nat) (target : Fin n)
    (T F : Finset (Fin n)) (root : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size) (observed : List (Word width))
    (fits : 1 < 2 ^ width)
    (witness : QueryChannelWitness heap layout (SharedZeroSource.references graph b target T F base slot root)
      n (by omega) observed) :
    Admissible b target (decode observed n) ∧ ExtendsFixed T F (decode observed n) ∧
      graph.eval (assignmentOfSet (decode observed n)) root = false := by
  let refs := SharedZeroSource.references graph b target T F base slot root
  let dictionary := constructorDictionary heap layout (empty _) refs
  obtain ⟨queue, previous, localModel, greatest, output⟩ := witness
  have coherent : Coherent dictionary := (rows_dictionary (empty _) (empty_coherent _)
    (ForestZeroAssembly.originalRows (reservedReferences refs))).1
  let assignment := ForestZeroModelLift.lift dictionary true
    (extendNat (Controller.Horn.WorklistOutcome.offAssignment queue))
  have original := (SharedZeroModel.constructor_lift_model heap layout (empty _) (empty_coherent _) refs n
    (by omega) (fun values model => SharedZeroMeaning.source_nonempty graph b target T F root values model) _).mp localModel
  have template : Satisfies assignment (SharedZeroTemplate.formula graph b target root T F) := by
    rw [SharedZeroSource.originalRows_eq] at original
    simpa [ofClauses, assignment, dictionary, refs] using original
  have projected := finite_model_projection graph guarded b target T F root assignment
    ((SharedZeroTemplate.satisfies_iff graph b target root T F assignment).mp template)
  have decoded : decode observed n = graph.zeroChannelSet (assignment ∘ graph.zeroIndex) := by
    rw [output]
    rw [queue_lift dictionary coherent queue]
    rw [decode_prefix _ _ fits]
    congr 1
  rw [decoded]
  exact projected

end Controller.Cost.SharedZeroOutput
