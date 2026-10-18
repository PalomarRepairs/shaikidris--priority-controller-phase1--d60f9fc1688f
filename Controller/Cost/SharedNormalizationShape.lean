module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Cost.SharedZeroSource
public import Controller.Cost.SharedZeroModel

@[expose] public section

namespace Controller.Cost.SharedNormalizationShape
open Controller.CNF Controller.Cost.GateProgram

def profile (clauses : List (Clause (Fin n))) : List Nat :=
  clauses.map fun clause => (Controller.Horn.Worklist.compileClause clause).positives.length

theorem record_end (left : List (Clause (Fin n))) (right : List (Clause (Fin m))) (start : Nat)
    (same : profile left = profile right) :
    Controller.Horn.NormalizeLoop.recordOffset left start left.length =
      Controller.Horn.NormalizeLoop.recordOffset right start right.length := by
  simp only [Controller.Horn.NormalizeLoop.recordOffset, List.take_length]
  have mapped := congrArg (fun values : List Nat => (values.map (fun value => 3 + value)).sum) same
  simpa only [profile, List.map_map, Function.comp_def] using congrArg (start + ·) mapped

theorem incidence_length (clauses : List (Clause (Fin n))) (start : Nat) :
    (Controller.Horn.IndexScan.occurrences clauses start).length = (profile clauses).sum := by
  induction clauses generalizing start with
  | nil => rfl
  | cons clause rest ih =>
    simp only [Controller.Horn.IndexScan.occurrences, List.length_append, List.length_map,
      profile, List.map_cons, List.sum_cons]
    rw [ih]
    rfl

theorem native_base (left : List (Clause (Fin n))) (right : List (Clause (Fin m))) (start : Nat)
    (same : profile left = profile right) :
    Controller.Horn.NormalizeLoop.recordOffset left start left.length +
      2 * (Controller.Horn.IndexScan.occurrences left start).length =
    Controller.Horn.NormalizeLoop.recordOffset right start right.length +
      2 * (Controller.Horn.IndexScan.occurrences right start).length := by
  rw [record_end left right start same, incidence_length, incidence_length, same]

theorem negative_unit (label : Fin n) :
    (Controller.Horn.Worklist.compileClause [(label, false)]).positives.length = 0 := by
  simp [Controller.Horn.Worklist.compileClause, Controller.Horn.Worklist.tautologyCheck,
    Controller.Horn.Worklist.signedLabels, Controller.CNF.negate, Std.Sat.Literal.negate, Controller.Horn.Worklist.Rule.positives]

theorem negative_root_profile (before after : List (Clause (Fin n))) (left right : Fin n) :
    profile (before ++ [[(left, false)]] ++ after) =
      profile (before ++ [[(right, false)]] ++ after) := by
  simp [profile, negative_unit]


theorem source_root_profile (graph : Controller.Decoder.DAG n) (b : Nat) (target : Fin n)
    (T F : Finset (Fin n)) (left right : Fin graph.nodeCount) :
    profile (Controller.Cost.ForestZeroAssembly.originalRows
      (Controller.Cost.SharedZeroSource.references graph b target T F base slot left)) =
    profile (Controller.Cost.ForestZeroAssembly.originalRows
      (Controller.Cost.SharedZeroSource.references graph b target T F base slot right)) := by
  simp only [Controller.Cost.SharedZeroSource.references, Controller.Cost.ForestZeroAssembly.originalRows,
    List.map_append, List.map_cons, List.map_nil, Controller.Cost.SharedZeroCode.rootReference]
  simp [profile, negative_unit]

theorem source_root_native_base (graph : Controller.Decoder.DAG n) (b : Nat) (target : Fin n)
    (T F : Finset (Fin n)) (left right : Fin graph.nodeCount) (start : Nat) :
    let rowsLeft := Controller.Cost.ForestZeroAssembly.originalRows
      (Controller.Cost.SharedZeroSource.references graph b target T F base slot left)
    let rowsRight := Controller.Cost.ForestZeroAssembly.originalRows
      (Controller.Cost.SharedZeroSource.references graph b target T F base slot right)
    Controller.Horn.NormalizeLoop.recordOffset rowsLeft start rowsLeft.length +
      2 * (Controller.Horn.IndexScan.occurrences rowsLeft start).length =
    Controller.Horn.NormalizeLoop.recordOffset rowsRight start rowsRight.length +
      2 * (Controller.Horn.IndexScan.occurrences rowsRight start).length :=
  native_base _ _ start (source_root_profile graph b target T F left right)


theorem signed_labels_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (injective : Function.Injective f) (clause : Clause α) (sign : Bool) :
    Controller.Horn.Worklist.signedLabels (clause.map (fun literal => (f literal.1, literal.2))) sign =
      (Controller.Horn.Worklist.signedLabels clause sign).map f := by
  have selected : ((clause.map (fun literal => (f literal.1, literal.2))).filter
      (fun literal => decide (literal.2 = sign))).map Prod.fst =
      ((clause.filter (fun literal => decide (literal.2 = sign))).map Prod.fst).map f := by
    induction clause with
    | nil => rfl
    | cons literal rest ih =>
      simp only [List.map_cons, List.filter_cons]
      split_ifs <;> simp_all
  unfold Controller.Horn.Worklist.signedLabels
  rw [selected, List.dedup_map_of_injective injective]

theorem tautology_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (injective : Function.Injective f) (clause : Clause α) :
    Controller.Horn.Worklist.tautologyCheck (clause.map (fun literal => (f literal.1, literal.2))) =
      Controller.Horn.Worklist.tautologyCheck clause := by
  apply Bool.eq_iff_iff.mpr
  simp only [Controller.Horn.Worklist.tautologyCheck_eq_true, Controller.Horn.Tautological]
  constructor
  · rintro ⟨literal, member, opposite⟩
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨other, inside, equal⟩ := List.mem_map.mp opposite
    have label := injective (congrArg Prod.fst equal)
    have sign := congrArg Prod.snd equal
    refine ⟨source, present, ?_⟩
    have same : other = negate source := by
      apply Prod.ext
      · exact label
      · exact sign
    simpa only [same] using inside
  · rintro ⟨literal, member, opposite⟩
    refine ⟨(f literal.1, literal.2), List.mem_map.mpr ⟨literal, member, rfl⟩, ?_⟩
    exact List.mem_map.mpr ⟨negate literal, opposite, rfl⟩

theorem positives_length_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (injective : Function.Injective f) (clause : Clause α) :
    (Controller.Horn.Worklist.compileClause (clause.map (fun literal => (f literal.1, literal.2)))).positives.length =
      (Controller.Horn.Worklist.compileClause clause).positives.length := by
  simp only [Controller.Horn.Worklist.compileClause, tautology_map f injective, signed_labels_map f injective]
  split
  · rfl
  · cases negatives : Controller.Horn.Worklist.signedLabels clause false <;>
      simp [Controller.Horn.Worklist.Rule.positives]


theorem original_profile (dictionary : Controller.Cost.ForestZeroCompile.Dictionary ambient)
    (coherent : Controller.Cost.ForestZeroCompile.Coherent dictionary)
    (references : List (List (Controller.Cost.ForestZeroEmit.Reference ambient))) :
    profile (Controller.Cost.ForestZeroAdmissibleCaller.originalClauses dictionary coherent references) =
      profile (Controller.Cost.ForestZeroAssembly.originalRows references) := by
  let final := (Controller.Cost.ForestZeroCompile.compileRows dictionary
    (Controller.Cost.ForestZeroAssembly.originalRows (Controller.Cost.ForestZeroAdmissibleCaller.reservedReferences references))).1
  have finalCoherent : Controller.Cost.ForestZeroCompile.Coherent final :=
    (Controller.Cost.ForestZeroCompile.rows_dictionary dictionary coherent _).1
  let lookup : Fin final.coordinates.size → Fin ambient := fun index => final.coordinates[index.val]
  have injective : Function.Injective lookup := by
    intro left right equal
    have leftCell : final.coordinates[left.val]? = some (lookup left) := by simp [lookup]
    have rightCell : final.coordinates[right.val]? = some (lookup right) := by simp [lookup]
    have leftSlot := (finalCoherent (lookup left) left.val).mpr leftCell
    have rightSlot := (finalCoherent (lookup right) right.val).mpr rightCell
    rw [← equal] at rightSlot
    apply Fin.ext
    omega
  have related := Controller.Cost.SharedZeroModel.original_correspondence dictionary coherent references
  change List.Forall₂ _ _ _ at related
  generalize Controller.Cost.ForestZeroAdmissibleCaller.originalClauses dictionary coherent references = produced at related ⊢
  generalize Controller.Cost.ForestZeroAssembly.originalRows references = originals at related ⊢
  unfold profile
  induction related with
  | nil => rfl
  | @cons produced original outputs originals same rest ih =>
    have mapped : produced.map (fun literal => (lookup literal.1, literal.2)) = original := by
      induction same with
      | nil => rfl
      | @cons output source outs sources pair pairs ihLit =>
        have label : lookup output.1 = source.1 := by
          exact (Array.getElem?_eq_some_iff.mp pair.1).choose_spec
        simp only [List.map_cons, label, pair.2, ihLit]
    simp only [List.map_cons]
    rw [← mapped, positives_length_map lookup injective, ih]


theorem finite_clause_positives (row : Clause Nat) (bound : ∀ literal ∈ row, literal.1 < limit) :
    (Controller.Horn.Worklist.compileClause (Controller.Cost.ForestZeroCompile.finiteClause row bound)).positives.length =
      (Controller.Horn.Worklist.compileClause row).positives.length := by
  have same := positives_length_map Fin.val Fin.val_injective (Controller.Cost.ForestZeroCompile.finiteClause row bound)
  rw [Controller.Cost.ForestZeroAssembly.finiteClause_raw] at same
  exact same.symm

theorem constructor_profile (heap : Array (Word width))
    (layout : Controller.Cost.ForestZeroDictionary.Layout ambient heap.size)
    (dictionary : Controller.Cost.ForestZeroCompile.Dictionary ambient)
    (coherent : Controller.Cost.ForestZeroCompile.Coherent dictionary)
    (references : List (List (Controller.Cost.ForestZeroEmit.Reference ambient)))
    (channels : Nat) (within : channels ≤ ambient) :
    profile (Controller.Cost.ForestZeroAdmissibleCaller.constructorClauses heap layout dictionary coherent references channels within) =
    profile (Controller.Cost.ForestZeroAssembly.originalRows references) ++
      (if (Controller.Cost.ForestZeroNonempty.search
        (Controller.Cost.ForestZeroAdmissibleCaller.constructorDictionary heap layout dictionary references)
        ((Controller.Cost.ForestZeroAdmissibleCaller.constructorDictionary heap layout dictionary references).coordinates.size + 1)
        channels 0).reason = .covered then
        [(Controller.Horn.Worklist.compileClause (Controller.Cost.ForestZeroPositive.positiveClause
          (Controller.Cost.ForestZeroAdmissibleCaller.constructorDictionary heap layout dictionary references) channels)).positives.length]
      else []) := by
  unfold Controller.Cost.ForestZeroAdmissibleCaller.constructorClauses
  dsimp only
  split_ifs
  · change profile (_ ++ [_]) = _
    simp only [profile, List.map_append, List.map_cons, List.map_nil]
    rw [finite_clause_positives]
    exact congrArg (· ++ _) (original_profile dictionary coherent references)
  · simpa only [List.append_nil] using original_profile dictionary coherent references

theorem constructor_root_profile (graph : Controller.Decoder.DAG n) (b : Nat) (target : Fin n)
    (T F : Finset (Fin n)) (left right : Fin graph.nodeCount) (heap : Array (Word width))
    (layout : Controller.Cost.ForestZeroDictionary.Layout (n + graph.nodeCount) heap.size) :
    profile (Controller.Cost.ForestZeroAdmissibleCaller.constructorClauses heap layout
      (Controller.Cost.ForestZeroCompile.empty _) (Controller.Cost.ForestZeroCompile.empty_coherent _)
      (Controller.Cost.SharedZeroSource.references graph b target T F base slot left) n (by omega)) =
    profile (Controller.Cost.ForestZeroAdmissibleCaller.constructorClauses heap layout
      (Controller.Cost.ForestZeroCompile.empty _) (Controller.Cost.ForestZeroCompile.empty_coherent _)
      (Controller.Cost.SharedZeroSource.references graph b target T F base slot right) n (by omega)) := by
  rw [constructor_profile, constructor_profile, source_root_profile graph b target T F left right,
    Controller.Cost.SharedZeroSource.dictionary_root_irrel graph b target T F left right heap layout]

end Controller.Cost.SharedNormalizationShape
