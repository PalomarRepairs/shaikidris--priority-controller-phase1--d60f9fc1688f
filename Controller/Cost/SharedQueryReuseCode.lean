module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedRootQueryEntry

@[expose] public section

namespace Controller.Cost.SharedQueryReuseCode
open Controller.Cost.GateProgram Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroDictionary
open Controller.Cost.ForestZeroAdmissibleCaller Controller.Cost.ForestZeroEmit
open Controller.Native Controller.Native.SourceController Controller.Decoder
open Controller.Cost.SharedZeroNativeQuery

theorem constructor_heap_size_irrel (before after : Array (Word width))
    (beforeLayout : Layout ambient before.size) (afterLayout : Layout ambient after.size)
    (references : List (List (Reference ambient))) (channels : Nat) (size : before.size = after.size) :
    (constructorHeap before beforeLayout (empty _) references channels).size =
      (constructorHeap after afterLayout (empty _) references channels).size := by
  rw [constructorHeap_size, constructorHeap_size, size]

theorem native_base_heap_irrel (before after : Array (Word width))
    (beforeLayout : Layout ambient before.size) (afterLayout : Layout ambient after.size)
    (references : List (List (Reference ambient))) (channels : Nat) (within : channels ≤ ambient)
    (size : before.size = after.size) :
    nativeBase before beforeLayout references channels within =
      nativeBase after afterLayout references channels within := by
  have heapSize := constructor_heap_size_irrel before after beforeLayout afterLayout references channels size
  have clauses : (constructorFormula before beforeLayout (empty _) (empty_coherent _)
      references channels within).clauses.toList =
    (constructorFormula after afterLayout (empty _) (empty_coherent _)
      references channels within).clauses.toList := rfl
  unfold nativeBase
  dsimp only
  rw [heapSize]
  rfl

@[irreducible] def code (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry next : Nat) (root : Fin graph.nodeCount) : List (Instruction width 8) :=
  let references := SharedZeroSource.references graph parameters.buses parameters.bridge.target T F coordinateBase slot root
  SharedQueryDispatch.code parameters width entry heap.size
    (constructorDictionary heap layout (empty _) references).coordinates.size
    (constructorHeap heap layout (empty _) references parameters.channels).size
    (nativeBase heap layout references parameters.channels (by omega)) references next

theorem root_irrel (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (heap : Array (Word width))
    (layout : Layout (parameters.channels + graph.nodeCount) heap.size)
    (coordinateBase slot entry next : Nat) (left right : Fin graph.nodeCount) :
    code parameters graph T F heap layout coordinateBase slot entry next left =
      code parameters graph T F heap layout coordinateBase slot entry next right := by
  unfold code
  dsimp only
  rw [SharedZeroSource.constructor_heap_size_root_irrel graph parameters.buses parameters.bridge.target T F left right heap layout,
    nativeBase_root_irrel parameters graph T F left right heap layout]
  simp only [SharedZeroSource.dictionary_size]
  unfold SharedQueryDispatch.code
  rw [SharedQueryResidentCode.root_code_irrel parameters graph parameters.buses parameters.bridge.target T F]

theorem heap_irrel (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (before after : Array (Word width))
    (beforeLayout : Layout (parameters.channels + graph.nodeCount) before.size)
    (afterLayout : Layout (parameters.channels + graph.nodeCount) after.size)
    (coordinateBase slot entry next : Nat) (root : Fin graph.nodeCount) (size : before.size = after.size) :
    code parameters graph T F before beforeLayout coordinateBase slot entry next root =
      code parameters graph T F after afterLayout coordinateBase slot entry next root := by
  unfold code
  dsimp only
  rw [constructor_heap_size_irrel before after beforeLayout afterLayout _ _ size,
    native_base_heap_irrel before after beforeLayout afterLayout _ _ _ size, size]

theorem shared (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (before after : Array (Word width))
    (beforeLayout : Layout (parameters.channels + graph.nodeCount) before.size)
    (afterLayout : Layout (parameters.channels + graph.nodeCount) after.size)
    (coordinateBase slot entry next : Nat) (left right : Fin graph.nodeCount) (size : before.size = after.size) :
    code parameters graph T F before beforeLayout coordinateBase slot entry next left =
      code parameters graph T F after afterLayout coordinateBase slot entry next right :=
  (root_irrel parameters graph T F before beforeLayout coordinateBase slot entry next left right).trans
    (heap_irrel parameters graph T F before after beforeLayout afterLayout coordinateBase slot entry next right size)

end Controller.Cost.SharedQueryReuseCode
