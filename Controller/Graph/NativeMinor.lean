module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Graph.Minor
public import Controller.Graph.NetWidth
public import Controller.Native.Encode

@[expose] public section

/-! Complete-bipartite width and native clause graphs. -/
namespace Controller.Graph

namespace TreeDecomposition
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- A deepest highest-occurrence bag contains a vertex and every neighbor.
This gives the minimum-degree lower bound without a Graph Minors theorem. -/
theorem closedNeighborhood_bag (D : TreeDecomposition G) (nonempty : Nonempty V) :
    ∃ v, ∀ u, u = v ∨ G.Adj u v → u ∈ D.bag (D.home v) := by
  obtain ⟨start⟩ := nonempty
  obtain ⟨v, hv⟩ := Finset.univ.exists_maximalFor D.home
    (show (Finset.univ : Finset V).Nonempty from ⟨start, Finset.mem_univ _⟩)
  refine ⟨v, ?_⟩
  intro u h
  rcases h with h | h
  · simpa only [h] using D.home_mem v
  obtain ⟨i, hui, hvi⟩ := D.edge h
  have hu := D.above_home u i hui
  have hv' := D.above_home v i hvi
  have huv : D.home u ≤ D.home v := by
    rcases le_total_of_directed hu hv' with h | h
    · exact hv.2 (Finset.mem_univ _) h
    · exact h
  exact D.interval u i (D.home v) hui huv hv'

end TreeDecomposition

noncomputable def bipartiteBag (n b : ℕ) (index : Fin (b + 1)) :
    Finset (Fin n ⊕ Fin b) := by
  classical
  exact Finset.univ.filter fun v => match v with
    | .inl _ => True
    | .inr j => index.val = j.val + 1

/-- All left vertices in each bag and one right vertex at a time. -/
noncomputable def bipartiteDecomposition (n b : ℕ) :
    TreeDecomposition (completeBipartiteGraph (Fin n) (Fin b)) where
  tree := NetSystem.pathTree b
  finite := inferInstanceAs (Fintype (Fin (b + 1)))
  bag := bipartiteBag n b
  home v := match v with
    | .inl _ => ⟨0, by omega⟩
    | .inr j => ⟨j.val + 1, by omega⟩
  home_mem v := by classical
                   cases v <;> simp [bipartiteBag]
  above_home v i h := by
    classical
    cases v with
    | inl u => change 0 ≤ i.val; omega
    | inr j =>
      change j.val + 1 ≤ i.val
      have : i.val = j.val + 1 := by simpa [bipartiteBag] using h
      omega
  interval v i j hi hj hji := by
    classical
    cases v with
    | inl u => simp [bipartiteBag]
    | inr u =>
      change u.val + 1 ≤ j.val at hj
      change j.val ≤ i.val at hji
      have : i.val = u.val + 1 := by simpa [bipartiteBag] using hi
      simp only [bipartiteBag, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  edge := by
    classical
    intro u v h
    cases u with
    | inl i =>
      cases v with
      | inl k => simp [completeBipartiteGraph] at h
      | inr j => exact ⟨⟨j.val + 1, by omega⟩, by simp [bipartiteBag],
          by simp [bipartiteBag]⟩
    | inr j =>
      cases v with
      | inr k => simp [completeBipartiteGraph] at h
      | inl i => exact ⟨⟨j.val + 1, by omega⟩, by simp [bipartiteBag],
          by simp [bipartiteBag]⟩

theorem bipartiteDecomposition_capacity (n b : ℕ) :
    (bipartiteDecomposition n b).Capacity (n + 1) := by
  classical
  intro i
  let f : (bipartiteDecomposition n b).bag i → Fin n ⊕ Unit := fun v =>
    match v.val with
    | .inl u => .inl u
    | .inr _ => .inr ()
  have injective : Function.Injective f := by
    intro ⟨u, hu⟩ ⟨v, hv⟩ eq
    apply Subtype.ext
    cases u with
    | inl u =>
      cases v with
      | inl v => simpa [f] using eq
      | inr v => simp [f] at eq
    | inr u =>
      cases v with
      | inl v => simp [f] at eq
      | inr v =>
        have hu : i.val = u.val + 1 := by simpa [bipartiteDecomposition, bipartiteBag] using hu
        have hv : i.val = v.val + 1 := by simpa [bipartiteDecomposition, bipartiteBag] using hv
        exact congrArg Sum.inr (Fin.ext (by omega))
  have bound := Fintype.card_le_of_injective f injective
  simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] using bound

private def leftStar (i : Fin n) : Option (Fin b) → Fin n ⊕ Fin b
  | none => .inl i
  | some j => .inr j

private theorem leftStar_injective (i : Fin n) : Function.Injective (leftStar (b := b) i) := by
  intro x y eq
  cases x <;> cases y <;> simp_all [leftStar]

private def rightStar (j : Fin b) : Option (Fin n) → Fin n ⊕ Fin b
  | none => .inr j
  | some i => .inl i

private theorem rightStar_injective (j : Fin b) : Function.Injective (rightStar (n := n) j) := by
  intro x y eq
  cases x <;> cases y <;> simp_all [rightStar]

/-- Every width bound for K_(n,b) is at least min(n,b), including empty sides. -/
theorem completeBipartite_treewidth_lower (n b w : ℕ)
    (bound : TreewidthLE (completeBipartiteGraph (Fin n) (Fin b)) w) :
    min n b ≤ w := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  by_cases hb : b = 0
  · simp [hb]
  obtain ⟨D, capacity⟩ := bound
  have nonempty : Nonempty (Fin n ⊕ Fin b) :=
    ⟨.inl ⟨0, by omega⟩⟩
  obtain ⟨v, contains⟩ := D.closedNeighborhood_bag nonempty
  cases v with
  | inl i =>
    have inside (x : Option (Fin b)) : leftStar i x ∈ D.bag (D.home (.inl i)) := by
      apply contains
      cases x with
      | none => exact Or.inl rfl
      | some j => exact Or.inr (by simp [leftStar, completeBipartiteGraph])
    have count := Fintype.card_le_of_injective
      (fun x => (⟨leftStar i x, inside x⟩ : D.bag (D.home (.inl i))))
      (fun x y eq => leftStar_injective i (congrArg Subtype.val eq))
    rw [Fintype.card_option, Fintype.card_fin, Fintype.card_coe] at count
    have room := capacity (D.home (.inl i))
    have := Nat.min_le_right n b
    omega
  | inr j =>
    have inside (x : Option (Fin n)) : rightStar j x ∈ D.bag (D.home (.inr j)) := by
      apply contains
      cases x with
      | none => exact Or.inl rfl
      | some i => exact Or.inr (by simp [rightStar, completeBipartiteGraph])
    have count := Fintype.card_le_of_injective
      (fun x => (⟨rightStar j x, inside x⟩ : D.bag (D.home (.inr j))))
      (fun x y eq => rightStar_injective j (congrArg Subtype.val eq))
    rw [Fintype.card_option, Fintype.card_fin, Fintype.card_coe] at count
    have room := capacity (D.home (.inr j))
    have := Nat.min_le_left n b
    omega

/-- Exact treewidth formula in the width-at-most vocabulary, also for empty sides. -/
theorem completeBipartite_treewidth_iff (n b w : ℕ) :
    TreewidthLE (completeBipartiteGraph (Fin n) (Fin b)) w ↔ min n b ≤ w := by
  constructor
  · exact completeBipartite_treewidth_lower n b w
  · intro h
    by_cases order : n ≤ b
    · refine ⟨bipartiteDecomposition n b, ?_⟩
      intro i
      exact (bipartiteDecomposition_capacity n b i).trans
        (Nat.add_le_add_right (by simpa [Nat.min_eq_left order] using h) 1)
    · have smaller : b ≤ n := by omega
      let D := bipartiteDecomposition b n
      have edges : ∀ ⦃u v : Fin n ⊕ Fin b⦄,
          (completeBipartiteGraph (Fin n) (Fin b)).Adj u v →
          (completeBipartiteGraph (Fin b) (Fin n)).Adj (Sum.swap u) (Sum.swap v) := by
        intro u v h
        cases u <;> cases v <;> simp_all [completeBipartiteGraph]
      refine ⟨D.comap Sum.swap edges, ?_⟩
      have injective : Function.Injective (Sum.swap : Fin n ⊕ Fin b → Fin b ⊕ Fin n) := by
        intro u v h
        simpa using congrArg Sum.swap h
      have capacity := D.comap_capacity Sum.swap injective edges (b + 1)
        (bipartiteDecomposition_capacity b n)
      intro i
      exact (capacity i).trans
        (Nat.add_le_add_right (by simpa [Nat.min_eq_right smaller] using h) 1)
end Controller.Graph

namespace Controller.Graph

variable {V : Type} [DecidableEq V]

/-- The primal graph of the complete clause list, independent of literal signs. -/
def clausePrimal (clauses : List (Controller.CNF.Clause V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ row ∈ clauses, u ∈ row.map Prod.fst ∧ v ∈ row.map Prod.fst
  symm := ⟨by
    intro u v h
    obtain ⟨ne, row, hr, hu, hv⟩ := h
    exact ⟨ne.symm, row, hr, hv, hu⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

omit [DecidableEq V] in
private theorem connected_star {G : SimpleGraph V} (S : Finset V) (hub : V)
    (member : hub ∈ S) (spokes : ∀ x ∈ S, x = hub ∨ G.Adj hub x) :
    ConnectedWithin G S := by
  refine ⟨⟨hub, member⟩, ?_⟩
  have paths (x : V) (hx : x ∈ S) :
      Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ G.Adj u v) x hub ∧
      Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ G.Adj u v) hub x := by
    rcases spokes x hx with eq | edge
    · subst x; exact ⟨.refl, .refl⟩
    · exact ⟨.single ⟨hx, member, edge.symm⟩, .single ⟨member, hx, edge⟩⟩
  intro u hu v hv
  exact (paths u hu).1.trans (paths v hv).2

namespace NativeWidth
open Controller.Native
open Controller.Native.Parameters

variable (p : Parameters)

def clauses : List (CNF.Clause (Variable p)) :=
  p.equationClauses ++ p.assertions.map (fun literal => [literal])

def primal : SimpleGraph (Variable p) := clausePrimal (clauses p)

def qualifier (i : Fin p.channels) : Variable p := .internal (.qualifier .faulty i)
def factor (i : Fin p.channels) (j : Fin p.buses) : Variable p :=
  .internal (.qualifierGuard .faulty j i)
def flag (j : Fin p.buses) : Variable p := .internal (.flag .faulty j)

private theorem row_mem {role : Internal p} {row : CNF.Clause (Variable p)}
    (h : row ∈ (p.gate role).clauses (internal p role)) : row ∈ clauses p := by
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨role, p.mem_roles role, h⟩

theorem qualifier_factor_adj (i : Fin p.channels) (j : Fin p.buses) :
    (primal p).Adj (qualifier p i) (factor p i j) := by
  refine ⟨by simp [qualifier, factor], ?_⟩
  refine ⟨[negative (qualifier p i), positive (factor p i j)], ?_, ?_, ?_⟩
  · apply row_mem p (role := .qualifier .faulty i)
    change _ ∈ (CNF.Gate.and _).clauses _
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨internal p (.qualifierGuard .faulty j i), ?_, rfl⟩
    simp [List.mem_map]
  · simp [negative]
  · simp [positive]

theorem factor_flag_adj (i : Fin p.channels) (j : Fin p.buses) :
    (primal p).Adj (factor p i j) (flag p j) := by
  refine ⟨by simp [factor, flag], ?_⟩
  refine ⟨[positive (factor p i j), positive (flag p j)], ?_, ?_, ?_⟩
  · apply row_mem p (role := .qualifierGuard .faulty j i)
    simp [gate, CNF.Gate.clauses, factor, flag, internal, positive, negative, CNF.negate,
      Std.Sat.Literal.negate]
  · simp [positive]
  · simp [positive]

def channelBranch (i : Fin p.channels) : Finset (Variable p) :=
  insert (qualifier p i) (Finset.univ.image (factor p i))

/-- Explicit branch sets in the uncontracted complete native primal graph. -/
def primalMinor : MinorModel (completeBipartiteGraph (Fin p.channels) (Fin p.buses))
    (primal p) where
  branch v := match v with
    | .inl i => channelBranch p i
    | .inr j => {flag p j}
  connected v := by
    cases v with
    | inl i =>
      apply connected_star _ (qualifier p i) (Finset.mem_insert_self _ _)
      intro x hx
      rcases Finset.mem_insert.mp hx with eq | member
      · exact Or.inl eq
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp member
      exact Or.inr (qualifier_factor_adj p i j)
    | inr j =>
      apply connected_star _ (flag p j) (Finset.mem_singleton_self _)
      intro x hx
      exact Or.inl (Finset.mem_singleton.mp hx)
  disjoint := by
    intro u v ne
    cases u <;> cases v <;>
      simp_all [channelBranch, qualifier, factor, flag, Finset.disjoint_left]
    all_goals simp_all [eq_comm]
  edge := by
    intro u v h
    cases u with
    | inl i =>
      cases v with
      | inl k => simp [completeBipartiteGraph] at h
      | inr j => exact ⟨factor p i j, Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩),
          flag p j, Finset.mem_singleton_self _, factor_flag_adj p i j⟩
    | inr j =>
      cases v with
      | inr k => simp [completeBipartiteGraph] at h
      | inl i => exact ⟨flag p j, Finset.mem_singleton_self _, factor p i j,
          Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩),
          (factor_flag_adj p i j).symm⟩

theorem primal_treewidth_lower (w : ℕ) (bound : TreewidthLE (primal p) w) :
    min p.channels p.buses ≤ w :=
  completeBipartite_treewidth_lower _ _ _ ((primalMinor p).treewidth_mono bound)

/-- Every equation row retains its producer and its position in that producer's
complete block. Assertion rows have separate positions. Duplicate rows remain
distinct occurrences. Flattening these blocks is `equationClauses`. -/
abbrev EquationAddress := (role : Internal p) ×
  Fin ((p.gate role).clauses (internal p role)).length

abbrev RowAddress := EquationAddress p ⊕ Fin p.assertions.length
abbrev IncidenceVertex := Variable p ⊕ RowAddress p

def rowClause : RowAddress p → CNF.Clause (Variable p)
  | .inl ⟨role, index⟩ => ((p.gate role).clauses (internal p role))[index.val]
  | .inr index => [p.assertions[index.val]]

def rowAddresses : List (RowAddress p) :=
  (p.roles.flatMap fun role =>
    (List.finRange ((p.gate role).clauses (internal p role)).length).map
      (fun index => Sum.inl ⟨role, index⟩)) ++
    (List.finRange p.assertions.length).map Sum.inr

def rowRole : RowAddress p → Option (Internal p)
  | .inl ⟨role, _⟩ => some role
  | .inr _ => none

theorem mem_rowAddresses (row : RowAddress p) : row ∈ rowAddresses p := by
  cases row with
  | inl row =>
    obtain ⟨role, index⟩ := row
    exact List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨role, p.mem_roles role, List.mem_map.mpr ⟨index, by simp, rfl⟩⟩)
  | inr index =>
    exact List.mem_append_right _ (List.mem_map.mpr ⟨index, by simp, rfl⟩)

/-- Addresses enumerate occurrences once, even when clause contents coincide. -/
theorem rowAddresses_nodup : (rowAddresses p).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨?_, (List.nodup_finRange _).map Sum.inr_injective, ?_⟩
  · apply List.nodup_flatMap.mpr
    constructor
    · intro role _
      apply (List.nodup_finRange _).map
      intro i j h
      simpa using h
    · apply p.roles_nodup.imp
      intro role other ne
      apply List.disjoint_left.mpr
      intro row hrow hother
      obtain ⟨i, _, hi⟩ := List.mem_map.mp hrow
      obtain ⟨j, _, hj⟩ := List.mem_map.mp hother
      have eq := congrArg (rowRole p) (hi.trans hj.symm)
      exact ne (Option.some.inj eq)
  · intro row hrow other hassertion equal
    obtain ⟨role, _, hrole⟩ := List.mem_flatMap.mp hrow
    obtain ⟨index, _, hindex⟩ := List.mem_map.mp hrole
    obtain ⟨assertion, _, heq⟩ := List.mem_map.mp hassertion
    have eq := congrArg (rowRole p) (hindex.trans (equal.trans heq.symm))
    simp [rowRole] at eq

/-- Naming rows by producer and position reproduces the complete clause list. -/
theorem rowAddresses_clauses : (rowAddresses p).map (rowClause p) = clauses p := by
  simp only [rowAddresses, List.map_append, List.map_flatMap, List.map_map,
    Function.comp_def, rowClause, clauses, equationClauses]
  congr 1
  · congr 1
    funext role
    rw [← List.ofFn_eq_map]
    exact List.ofFn_getElem

theorem clauses_specification : CNF.ofClauses (clauses p) = p.specificationFormula := by
  change (⟨(p.equationClauses ++ p.assertions.map (fun literal => [literal])).toArray⟩ :
    CNF.Formula (Variable p)) =
      ⟨p.equationClauses.toArray ++ (p.assertions.map (fun literal => [literal])).toArray⟩
  rw [List.append_toArray]

def incidenceAdj : IncidenceVertex p → IncidenceVertex p → Prop
  | .inl v, .inr row => v ∈ (rowClause p row).map Prod.fst
  | .inr row, .inl v => v ∈ (rowClause p row).map Prod.fst
  | _, _ => False

def incidence : SimpleGraph (IncidenceVertex p) where
  Adj := incidenceAdj p
  symm := ⟨by intro u v h; cases u <;> cases v <;> exact h⟩
  loopless := ⟨by intro v h; cases v <;> exact h⟩

/-- Choose an actual row position, with no clause normalization. -/
def address (role : Internal p) (row : CNF.Clause (Variable p))
    (member : row ∈ (p.gate role).clauses (internal p role)) : EquationAddress p :=
  ⟨role, ⟨((p.gate role).clauses (internal p role)).idxOf row,
    List.idxOf_lt_length_of_mem member⟩⟩

@[simp] theorem rowClause_address (role : Internal p) (row : CNF.Clause (Variable p))
    (member : row ∈ (p.gate role).clauses (internal p role)) :
    rowClause p (.inl (address p role row member)) = row := by
  exact List.getElem_idxOf _

theorem qualifier_row (i : Fin p.channels) (j : Fin p.buses) :
    [negative (qualifier p i), positive (factor p i j)] ∈
      (p.gate (.qualifier .faulty i)).clauses (internal p (.qualifier .faulty i)) := by
  change _ ∈ (CNF.Gate.and _).clauses _
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨internal p (.qualifierGuard .faulty j i), ?_, rfl⟩
  simp [List.mem_map]

theorem factor_row (i : Fin p.channels) (j : Fin p.buses) :
    [positive (factor p i j), positive (flag p j)] ∈
      (p.gate (.qualifierGuard .faulty j i)).clauses
        (internal p (.qualifierGuard .faulty j i)) := by
  simp [gate, CNF.Gate.clauses, factor, flag, internal, positive, negative,
    CNF.negate, Std.Sat.Literal.negate]

def andRow (i : Fin p.channels) (j : Fin p.buses) : IncidenceVertex p :=
  .inr (.inl (address p (.qualifier .faulty i)
    [negative (qualifier p i), positive (factor p i j)] (qualifier_row p i j)))

def orRow (i : Fin p.channels) (j : Fin p.buses) : IncidenceVertex p :=
  .inr (.inl (address p (.qualifierGuard .faulty j i)
    [positive (factor p i j), positive (flag p j)] (factor_row p i j)))

theorem incidence_arm_edges (i : Fin p.channels) (j : Fin p.buses) :
    (incidence p).Adj (.inl (qualifier p i)) (andRow p i j) ∧
    (incidence p).Adj (andRow p i j) (.inl (factor p i j)) ∧
    (incidence p).Adj (.inl (factor p i j)) (orRow p i j) ∧
    (incidence p).Adj (orRow p i j) (.inl (flag p j)) := by
  simp [incidence, incidenceAdj, andRow, orRow, positive, negative]

def incidenceChannelBranch (i : Fin p.channels) : Finset (IncidenceVertex p) :=
  insert (.inl (qualifier p i)) (Finset.univ.biUnion fun j =>
    {andRow p i j, .inl (factor p i j), orRow p i j})

def owner : IncidenceVertex p → Option (Fin p.channels)
  | .inl (.internal (.qualifier _ i)) => some i
  | .inl (.internal (.qualifierGuard _ _ i)) => some i
  | .inr (.inl ⟨.qualifier _ i, _⟩) => some i
  | .inr (.inl ⟨.qualifierGuard _ _ i, _⟩) => some i
  | _ => none

theorem incidence_owner (i : Fin p.channels) {x : IncidenceVertex p}
    (member : x ∈ incidenceChannelBranch p i) : owner p x = some i := by
  rcases Finset.mem_insert.mp member with eq | member
  · subst x; rfl
  obtain ⟨j, _, member⟩ := Finset.mem_biUnion.mp member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with eq | eq | eq <;> subst x <;> rfl

theorem incidence_arm_mem (i : Fin p.channels) (j : Fin p.buses) :
    andRow p i j ∈ incidenceChannelBranch p i ∧
    (.inl (factor p i j) : IncidenceVertex p) ∈ incidenceChannelBranch p i ∧
    orRow p i j ∈ incidenceChannelBranch p i := by
  have contained : {andRow p i j, (.inl (factor p i j) : IncidenceVertex p), orRow p i j} ⊆
      incidenceChannelBranch p i := by
    intro x hx
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hx⟩)
  exact ⟨contained (by simp), contained (by simp), contained (by simp)⟩

theorem incidence_channel_connected (i : Fin p.channels) :
    ConnectedWithin (incidence p) (incidenceChannelBranch p i) := by
  let S := incidenceChannelBranch p i
  let q : IncidenceVertex p := .inl (qualifier p i)
  let R := fun x y => x ∈ S ∧ y ∈ S ∧ (incidence p).Adj x y
  let : Std.Symm R := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  have qmem : q ∈ S := Finset.mem_insert_self _ _
  have fromHub (x : IncidenceVertex p) (hx : x ∈ S) : Relation.ReflTransGen R q x := by
    rcases Finset.mem_insert.mp hx with eq | member
    · subst x; exact .refl
    obtain ⟨j, _, member⟩ := Finset.mem_biUnion.mp member
    have amem : andRow p i j ∈ S := (incidence_arm_mem p i j).1
    have fmem : (.inl (factor p i j) : IncidenceVertex p) ∈ S :=
      (incidence_arm_mem p i j).2.1
    have omem : orRow p i j ∈ S := (incidence_arm_mem p i j).2.2
    have edges := incidence_arm_edges p i j
    have toAnd : Relation.ReflTransGen R q (andRow p i j) :=
      .single ⟨qmem, amem, edges.1⟩
    have toFactor : Relation.ReflTransGen R q (.inl (factor p i j)) :=
      toAnd.tail ⟨amem, fmem, edges.2.1⟩
    have toOr : Relation.ReflTransGen R q (orRow p i j) :=
      toFactor.tail ⟨fmem, omem, edges.2.2.1⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with eq | eq | eq
    · exact eq.symm ▸ toAnd
    · exact eq.symm ▸ toFactor
    · exact eq.symm ▸ toOr
  refine ⟨⟨q, qmem⟩, ?_⟩
  intro u hu v hv
  exact (symm (fromHub u hu)).trans (fromHub v hv)

/-- Explicit clause-inclusive branches for the native incidence graph. -/
def incidenceMinor : MinorModel (completeBipartiteGraph (Fin p.channels) (Fin p.buses))
    (incidence p) where
  branch v := match v with
    | .inl i => incidenceChannelBranch p i
    | .inr j => {.inl (flag p j)}
  connected v := by
    cases v with
    | inl i => exact incidence_channel_connected p i
    | inr j =>
      apply connected_star (G := incidence p) _
        (Sum.inl (flag p j) : IncidenceVertex p) (Finset.mem_singleton_self _)
      intro x hx
      exact Or.inl (Finset.mem_singleton.mp hx)
  disjoint := by
    intro u v ne
    cases u with
    | inl i =>
      cases v with
      | inl k =>
        apply Finset.disjoint_left.mpr
        intro x hx hy
        have eq := (incidence_owner p i hx).symm.trans (incidence_owner p k hy)
        exact ne (congrArg Sum.inl (Option.some.inj eq))
      | inr j =>
        apply Finset.disjoint_left.mpr
        intro x hx hy
        have eq := incidence_owner p i hx
        have hx : x = .inl (flag p j) := Finset.mem_singleton.mp hy
        simp [hx, owner, flag] at eq
    | inr j =>
      cases v with
      | inl i =>
        apply Finset.disjoint_left.mpr
        intro x hx hy
        have eq := incidence_owner p i hy
        have hx : x = .inl (flag p j) := Finset.mem_singleton.mp hx
        simp [hx, owner, flag] at eq
      | inr k => simp_all [Finset.disjoint_singleton_left, flag]
  edge := by
    intro u v h
    cases u with
    | inl i =>
      cases v with
      | inl k => simp [completeBipartiteGraph] at h
      | inr j =>
        refine ⟨orRow p i j, ?_, .inl (flag p j), Finset.mem_singleton_self _,
          (incidence_arm_edges p i j).2.2.2⟩
        exact (incidence_arm_mem p i j).2.2
    | inr j =>
      cases v with
      | inr k => simp [completeBipartiteGraph] at h
      | inl i =>
        refine ⟨.inl (flag p j), Finset.mem_singleton_self _, orRow p i j, ?_,
          (incidence_arm_edges p i j).2.2.2.symm⟩
        exact (incidence_arm_mem p i j).2.2

theorem incidence_treewidth_lower (w : ℕ) (bound : TreewidthLE (incidence p) w) :
    min p.channels p.buses ≤ w :=
  completeBipartite_treewidth_lower _ _ _ ((incidenceMinor p).treewidth_mono bound)

end NativeWidth
end Controller.Graph
