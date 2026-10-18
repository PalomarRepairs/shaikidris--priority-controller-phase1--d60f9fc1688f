module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Native.Encode
public import Controller.Resolution.Trace
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! Ordered native clause occurrences bind to one-based resolution IDs.
Relabeling changes variables only: duplicate clauses and literal occurrences
retain their positions. The native variable map covers the declared universe. -/
namespace Controller.NativeProof.Rows
open Controller.CNF Controller.Resolution

noncomputable def variableEquiv (parameters : Controller.Native.Parameters) :
    Controller.Native.Variable parameters ≃ Fin (Fintype.card (Controller.Native.Variable parameters)) :=
  Fintype.equivFin _

def mapClause (rename : α → Fin v) (clause : Clause α) : Clause (Fin v) :=
  clause.map (fun literal => (rename literal.1, literal.2))

structure Available (state : State v) (clause : Clause (Fin v)) where
  id : Nat
  present : state.rows id = some clause
  bound : id ≤ state.lastId

theorem relabeled_row (rename : α → Fin v) (formula : Formula α)
    (index : Fin formula.clauses.size) :
    (initialState (relabel rename formula)).rows (index.val + 1) =
      some (mapClause rename formula.clauses[index.val]) := by
  have bound : index.val < (relabel rename formula).clauses.size := by
    simpa [relabel, Controller.CNF.OrderedFormula.relabel] using index.isLt
  simpa [relabel, Controller.CNF.OrderedFormula.relabel, Controller.CNF.OrderedFormula.Clause.relabel, mapClause] using
    initialState_row (relabel rename formula) index.val bound

def originalRow (rename : α → Fin v) (formula : Formula α)
    (index : Fin formula.clauses.size) :
    Available (initialState (relabel rename formula)) (mapClause rename formula.clauses[index.val]) where
  id := index.val + 1
  present := relabeled_row rename formula index
  bound := by
    simp only [initialState, relabel, Controller.CNF.OrderedFormula.relabel, Array.size_map]
    exact Nat.succ_le_of_lt index.isLt

@[simp] theorem originalRow_id (rename : α → Fin v) (formula : Formula α)
    (index : Fin formula.clauses.size) : (originalRow rename formula index).id = index.val + 1 := rfl

/-- Equal clause contents do not merge distinct original occurrences. -/
theorem originalRow_id_injective (rename : α → Fin v) (formula : Formula α) :
    Function.Injective (fun index : Fin formula.clauses.size => (originalRow rename formula index).id) := by
  intro left right equality
  apply Fin.ext
  simpa [originalRow] using equality

/-- An actual successful prefix preserves these original row identifiers. -/
def afterPrefix (rename : α → Fin v) (formula : Formula α) (index : Fin formula.clauses.size)
    (state : State v) (steps : List (Step v))
    (checked : runSteps (initialState (relabel rename formula)) steps = some state) :
    Available state (mapClause rename formula.clauses[index.val]) where
  id := index.val + 1
  present := (runSteps_preserves_old_rows checked _ (originalRow rename formula index).bound).trans
    (originalRow rename formula index).present
  bound := Nat.le_trans (originalRow rename formula index).bound (runSteps_lastId_le checked)

/-- A concrete occurrence inside a retained block has its own frame offset. -/
def framedRow (rename : α → Fin v) (before block after : List (Clause α))
    (index : Fin block.length) :
    Available (initialState (relabel rename (ofClauses (before ++ block ++ after))))
      (mapClause rename block[index.val]) := by
  let position : Fin (ofClauses (before ++ block ++ after)).clauses.size :=
    ⟨before.length + index.val, by simp [ofClauses]; omega⟩
  have listBound : before.length + index.val < (before ++ block ++ after).length := by
    simp only [List.length_append]; omega
  have content : (ofClauses (before ++ block ++ after)).clauses[position.val] = block[index.val] := by
    change (before ++ block ++ after)[before.length + index.val]'listBound = block[index.val]
    simp [List.getElem_append, position, index.isLt]
  rw [← content]
  exact originalRow rename (ofClauses (before ++ block ++ after)) position

def blockPrefix (parameters : Controller.Native.Parameters) (index : Fin parameters.roles.length) :=
  (parameters.roles.take index.val).flatMap fun owner =>
    (parameters.gate owner).clauses (parameters.internal owner)

def blockSuffix (parameters : Controller.Native.Parameters) (index : Fin parameters.roles.length) :=
  (parameters.roles.drop (index.val + 1)).flatMap fun owner =>
    (parameters.gate owner).clauses (parameters.internal owner)

theorem equationClauses_split (parameters : Controller.Native.Parameters)
    (index : Fin parameters.roles.length) :
    parameters.equationClauses = blockPrefix parameters index ++
      (parameters.gate parameters.roles[index.val]).clauses (parameters.internal parameters.roles[index.val]) ++
      blockSuffix parameters index := by
  have split : parameters.roles = parameters.roles.take index.val ++
      [parameters.roles[index.val]] ++ parameters.roles.drop (index.val + 1) := by
    calc
      parameters.roles = parameters.roles.take (index.val + 1) ++ parameters.roles.drop (index.val + 1) :=
        (List.take_append_drop _ _).symm
      _ = _ := by rw [List.take_succ_eq_append_getElem index.isLt]
  unfold Controller.Native.Parameters.equationClauses
  conv_lhs => rw [split]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    blockPrefix, blockSuffix]

/-- Every exact gate-clause occurrence in the native equation enumeration is
available without any observation assertion or external validity premise. -/
noncomputable def nativeGateRow (parameters : Controller.Native.Parameters)
    (owner : Fin parameters.roles.length)
    (index : Fin ((parameters.gate parameters.roles[owner.val]).clauses
      (parameters.internal parameters.roles[owner.val])).length) :
    Available (initialState (relabel (variableEquiv parameters) parameters.equationFormula))
      (mapClause (variableEquiv parameters)
        ((parameters.gate parameters.roles[owner.val]).clauses
          (parameters.internal parameters.roles[owner.val]))[index.val]) := by
  rw [Controller.Native.Parameters.equationFormula, equationClauses_split parameters owner]
  exact framedRow (variableEquiv parameters) (blockPrefix parameters owner) _ (blockSuffix parameters owner) index

end Controller.NativeProof.Rows
