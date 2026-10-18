module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.EnumerationUniformOracleCapacity

@[expose] public section

namespace Controller.Cost.EnumerationUniformOracle
open Controller.Decoder Controller.Native Controller.Native.SourceController
open Controller.Cost.NativeSourceExecution Controller.Cost.ForestIndexedOperands

/-- Prefix masks are runtime data and never change the resident instructions. -/
theorem code_prefix_irrel (parameters : Parameters) (graph : DAG parameters.channels)
    (T F T' F' : Finset (Fin parameters.channels)) (width : Nat)
    (rows : List Row) (roots : List Nat) (entry back : Nat) :
    code parameters graph T F width rows roots entry back =
      code parameters graph T' F' width rows roots entry back := by
  unfold code
  rfl

/-- The resident program has linear length in the stored DAG size. -/
theorem code_length_bound (parameters : Parameters) (graph : DAG parameters.channels)
    (T F : Finset (Fin parameters.channels)) (width : Nat)
    (rows : List Row) (roots : List Nat) (entry back : Nat) (matched : RootsMatch graph roots) :
    (code parameters graph T F width rows roots entry back).length ≤
      610 * (graph.countedSize + 1) + 1609 := by
  have endEq := code_length parameters graph T F width rows roots entry back matched
  have bound := teardownEntry_bound parameters graph T F width entry
  have size := graph.countedSize_eq
  omega

end Controller.Cost.EnumerationUniformOracle
