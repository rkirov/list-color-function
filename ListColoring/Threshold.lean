/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.ListColorFunction

/-!
# An explicit enumerative chromatic-choosability threshold, and Donner's theorem

Donner proved in 1992 that every graph is enumeratively chromatic-choosable at `k` for all
sufficiently large `k`; his proof is non-constructive and gives no threshold. This file proves an
explicit — if crude — threshold,

`k > 2 ^ m  ⟹  G is enumeratively chromatic-choosable at `k``,   `m = |E(G)|`,

and deduces Donner's statement from it.  (Wang, Qian and Yan have since brought the threshold down
to `(m-1) / ln (1 + √2)`; their argument runs over the *broken cycle* / NBC form of Whitney's
theorem, which Mathlib does not have, whereas everything below is self-contained.)

## The argument

Write `n = |V|`, `E = E(G)`, `m = |E|`, and for `S ⊆ E` let `c(S)` be the number of connected
components of the spanning subgraph `(V, S)`.

*Step 1* (`listCount_eq_prod`, `col_eq_sum_powerset`).  Inclusion–exclusion over `E` expands the
list coloring count as `col(G, L) = ∑_{S ⊆ E} (-1)^{|S|} N_L(S)`, where
`N_L(S) = ∏_C |⋂_{v ∈ C} L v|` is the number of colorings from `L` constant on every edge of `S`,
the product running over the components `C` of `(V, S)`.  For the constant list this is the Whitney
expansion of the chromatic polynomial, `N_{[k]}(S) = k ^ c(S)`, so subtracting gives
`col(G, L) - col(G, k) = ∑_{S ⊆ E} (-1)^{|S|+1} d(S)` with `d(S) = k^{c(S)} - N_L(S) ≥ 0`
(`col_sub_colConst_eq`, `whitneyDefect`).

*Step 2* (`pow_card_le_prod_add_pow_mul_sum`).  A product of `c` factors each at most `k` falls
short of `k ^ c` by at most `k^{c-1}` times the total shortfall of the factors.

*Step 3* (`sub_card_listInter_insert_le`, `sum_sub_card_compInter_le`).  The deficiency
`k - |⋂_{v ∈ W} L v|` of a set of vertices grows by at most `k - |L u ∩ L w|` when a vertex `w`
joined to `u ∈ W` is adjoined.  Growing each component one boundary edge at a time bounds the total
deficiency of the components of `(V, S)` by `t = ∑_{e ∈ S} (k - |L u ∩ L v|)`.

*Step 4* (`compCount_le_of_two_le`).  Two distinct edges of a simple graph span at least three
vertices and merge two independent pairs, so `c(S) ≤ n - 2` as soon as `|S| ≥ 2`.

Together: the `|S| = 1` terms contribute exactly `k^{n-2} · t` (`pow_sub_listCount_singleton`), the
term `S = ∅` contributes nothing, and each of the fewer than `2 ^ m` remaining terms is at most
`k^{n-3} · t`, so the difference is at least `t · k^{n-3} · (k - 2^m) ≥ 0`.  Note that `t ≥ 0`
always, so — unlike in the sharp form of the theorem — no connectivity hypothesis is needed.

## Main results

* `SimpleGraph.listCount_eq_prod` : the list version of `card_filter_constOnEdges`
* `SimpleGraph.col_eq_sum_powerset` : the Whitney expansion of `col(G, L)`
* `SimpleGraph.pow_card_le_prod_add_pow_mul_sum` : Step 2, the telescoping bound
* `SimpleGraph.sum_sub_card_compInter_le` : Step 3, deficiency is subadditive along edges
* `SimpleGraph.ecc_of_two_pow_lt` : `2 ^ m < k → G.ECCAt k`
* `SimpleGraph.exists_ecc_forall_ge` : Donner's theorem
* `SimpleGraph.listColorFunction_eq_eval_of_two_pow_lt` : the same as `P_ℓ(G, k) = P(G, k)`
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Intersecting the lists over a set of vertices -/

/-- `⋂_{v ∈ U} L v`, as a `Finset ℕ`.  For `U = ∅` this returns `∅` rather than "all colors";
every use below has `U` nonempty. -/
def listInter (L : ListAssignment V) (U : Finset V) : Finset ℕ :=
  {a ∈ U.biUnion L | ∀ v ∈ U, a ∈ L v}

lemma mem_listInter {L : ListAssignment V} {U : Finset V} (hU : U.Nonempty) {a : ℕ} :
    a ∈ listInter L U ↔ ∀ v ∈ U, a ∈ L v := by
  simp only [listInter, mem_filter, mem_biUnion]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨v, hv⟩ := hU
  exact ⟨v, hv, h v hv⟩

lemma listInter_subset {L : ListAssignment V} {U : Finset V} {v : V} (hv : v ∈ U) :
    listInter L U ⊆ L v :=
  fun _ ha => (mem_listInter ⟨v, hv⟩).mp ha v hv

lemma listInter_insert (L : ListAssignment V) {U : Finset V} (hU : U.Nonempty) (w : V) :
    listInter L (insert w U) = listInter L U ∩ L w := by
  ext a
  rw [mem_listInter (Finset.insert_nonempty w U), mem_inter, mem_listInter hU,
    Finset.forall_mem_insert]
  exact and_comm

/-- The deficiency of an edge: how many of the `k` colors are lost by intersecting the two lists
at its ends. -/
def edgeDef (L : ListAssignment V) (k : ℕ) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun u v => k - #(L u ∩ L v), fun u v => by simp [Finset.inter_comm]⟩

omit [Fintype V] [DecidableEq V] in
@[simp] lemma edgeDef_mk (L : ListAssignment V) (k : ℕ) (u v : V) :
    edgeDef L k s(u, v) = k - #(L u ∩ L v) := rfl

/-! ### Components of a spanning subgraph, as finsets -/

/-- The spanning subgraph of `V` with edge set `S` (loops in `S` are discarded). -/
abbrev edgeGraph (S : Finset (Sym2 V)) : SimpleGraph V := fromEdgeSet (S : Set (Sym2 V))

/-- The vertices of a connected component of `edgeGraph S`, as a `Finset`. -/
def compFinset (S : Finset (Sym2 V)) (C : (edgeGraph S).ConnectedComponent) : Finset V :=
  Finset.univ.filter (fun v => v ∈ C.supp)

@[simp] lemma mem_compFinset {S : Finset (Sym2 V)} {C : (edgeGraph S).ConnectedComponent} {v : V} :
    v ∈ compFinset S C ↔ (edgeGraph S).connectedComponentMk v = C := by
  simp [compFinset]

lemma compFinset_nonempty (S : Finset (Sym2 V)) (C : (edgeGraph S).ConnectedComponent) :
    (compFinset S C).Nonempty := by
  induction C using ConnectedComponent.ind with
  | _ v => exact ⟨v, by simp⟩

/-- `⋂_{v ∈ C} L v` for a connected component `C` of `edgeGraph S`. -/
def compInter (L : ListAssignment V) (S : Finset (Sym2 V))
    (C : (edgeGraph S).ConnectedComponent) : Finset ℕ :=
  listInter L (compFinset S C)

lemma compInter_subset {L : ListAssignment V} {S : Finset (Sym2 V)}
    {C : (edgeGraph S).ConnectedComponent} {v : V}
    (hv : (edgeGraph S).connectedComponentMk v = C) : compInter L S C ⊆ L v :=
  listInter_subset (mem_compFinset.mpr hv)

/-! ### The list Whitney expansion -/

/-- The number of colorings of `V` from the lists `L` that are constant on every edge of `S`. -/
def listCount (L : ListAssignment V) (S : Finset (Sym2 V)) : ℕ :=
  #{f ∈ Fintype.piFinset L | ∀ e ∈ S, ConstOnEdge f e}

/-- **The key counting lemma, for arbitrary lists.**  A coloring from `L` that is constant on every
edge of `S` is exactly a choice, for each connected component `C` of `(V, S)`, of a color lying in
*all* the lists of `C`.  This generalizes `card_filter_constOnEdges`, which is the case of the
constant list assignment. -/
theorem listCount_eq_prod (L : ListAssignment V) (S : Finset (Sym2 V)) :
    listCount L S = ∏ C : (edgeGraph S).ConnectedComponent, #(compInter L S C) := by
  classical
  set H : SimpleGraph V := edgeGraph S with hH
  have key : #(Fintype.piFinset fun C : H.ConnectedComponent => compInter L S C) =
      #{f ∈ Fintype.piFinset L | ∀ e ∈ S, ConstOnEdge f e} := by
    refine Finset.card_bij (fun g _ v => g (H.connectedComponentMk v)) ?_ ?_ ?_
    · intro g hg
      rw [Fintype.mem_piFinset] at hg
      rw [mem_filter, Fintype.mem_piFinset]
      exact ⟨fun v => compInter_subset rfl (hg _), forall_constOnEdge_iff.mpr fun v w hvw => by
        rw [ConnectedComponent.connectedComponentMk_eq_of_adj hvw]⟩
    · intro g₁ _ g₂ _ h
      funext C
      induction C using ConnectedComponent.ind with
      | _ v => exact congrFun h v
    · intro f hf
      rw [mem_filter, Fintype.mem_piFinset] at hf
      have hconst : ∀ v w, H.Adj v w → f v = f w := forall_constOnEdge_iff.mp hf.2
      refine ⟨ConnectedComponent.lift f fun v w p _ => eq_of_reachable_of_adj_imp_eq hconst ⟨p⟩,
        ?_, rfl⟩
      rw [Fintype.mem_piFinset]
      intro C
      induction C using ConnectedComponent.ind with
      | _ v =>
        rw [compInter, mem_listInter (compFinset_nonempty S _)]
        intro w hw
        have : f w = f v :=
          eq_of_reachable_of_adj_imp_eq hconst (ConnectedComponent.exact (mem_compFinset.mp hw))
        rw [show (ConnectedComponent.lift f
          (fun v w p _ => eq_of_reachable_of_adj_imp_eq hconst ⟨p⟩) (H.connectedComponentMk v))
            = f v from rfl, ← this]
        exact hf.1 w
  rw [listCount, ← key, Fintype.card_piFinset]

/-- The `ℤ`-valued form of `listCount_eq_prod`'s left-hand side, for the inclusion–exclusion
computation. -/
theorem sum_prod_constOnEdge_indicator_list (L : ListAssignment V) (S : Finset (Sym2 V)) :
    (∑ f ∈ Fintype.piFinset L, ∏ e ∈ S, if ConstOnEdge f e then (1 : ℤ) else 0)
      = (listCount L S : ℤ) := by
  have key : ∀ f : V → ℕ, (∏ e ∈ S, if ConstOnEdge f e then (1 : ℤ) else 0)
      = if ∀ e ∈ S, ConstOnEdge f e then (1 : ℤ) else 0 := by
    intro f
    by_cases h : ∀ e ∈ S, ConstOnEdge f e
    · rw [if_pos h]
      exact Finset.prod_eq_one fun e he => if_pos (h e he)
    · rw [if_neg h]
      push Not at h
      obtain ⟨e, he, hne⟩ := h
      exact Finset.prod_eq_zero he (if_neg hne)
  simp_rw [key]
  rw [sum_ite_one_zero, listCount]

section Expansion

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The Whitney expansion of the list coloring count.**  Exactly as for the chromatic polynomial
(`eval_chromaticPolynomial`), inclusion–exclusion over the edge set turns `col(G, L)` into an
alternating sum of the counts `listCount L S`.  Taking `L` constant recovers the chromatic
polynomial, since `listCount (constList V k) S = k ^ c(S)`. -/
theorem col_eq_sum_powerset (L : ListAssignment V) :
    (G.col L : ℤ) = ∑ S ∈ G.edgeFinset.powerset, (-1) ^ #S * (listCount L S : ℤ) := by
  rw [col, colorings, ← sum_ite_one_zero]
  calc (∑ f ∈ Fintype.piFinset L, if G.IsProperColoring f then (1 : ℤ) else 0)
      = ∑ f ∈ Fintype.piFinset L, ∑ S ∈ G.edgeFinset.powerset,
          (-1) ^ #S * ∏ e ∈ S, if ConstOnEdge f e then (1 : ℤ) else 0 := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← prod_one_sub_eq_sum_powerset, prod_one_sub_indicator]
    _ = ∑ S ∈ G.edgeFinset.powerset, ∑ f ∈ Fintype.piFinset L,
          (-1) ^ #S * ∏ e ∈ S, if ConstOnEdge f e then (1 : ℤ) else 0 := Finset.sum_comm
    _ = ∑ S ∈ G.edgeFinset.powerset, (-1) ^ #S * (listCount L S : ℤ) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [← Finset.mul_sum, sum_prod_constOnEdge_indicator_list]

/-- For the constant list assignment the count is `k ^ c(S)`: this is
`card_filter_constOnEdges`. -/
theorem listCount_constList (k : ℕ) (S : Finset (Sym2 V)) :
    listCount (constList V k) S = k ^ compCount S :=
  card_filter_constOnEdges S k

end Expansion

/-! ### Step 2: a telescoping bound for a product of bounded factors

If every factor of a product of `c` terms is at most `k`, the product falls short of `k ^ c` by at
most `k ^ (c-1)` times the total shortfall of the factors.  The exponent is left as a free
parameter `p` (any `p` with `#s ≤ p + 1` will do), which keeps truncated subtraction out of the
statement. -/

theorem pow_card_le_prod_add_pow_mul_sum {ι : Type*} [DecidableEq ι] {k : ℕ} (hk : 1 ≤ k)
    (a : ι → ℕ) (s : Finset ι) (p : ℕ) (ha : ∀ i ∈ s, a i ≤ k) (hs : #s ≤ p + 1) :
    k ^ #s ≤ (∏ i ∈ s, a i) + k ^ p * ∑ i ∈ s, (k - a i) := by
  induction s using Finset.induction_on generalizing p with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.card_insert_of_notMem hj]
    rw [Finset.card_insert_of_notMem hj] at hs
    have haj : a j ≤ k := ha j (Finset.mem_insert_self j s)
    have ha' : ∀ i ∈ s, a i ≤ k := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    match p with
    | 0 =>
      have hs0 : s = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hs0
      simp only [Finset.prod_empty, Finset.sum_empty, mul_one, add_zero, pow_zero,
        Finset.card_empty, zero_add, pow_one, one_mul]
      omega
    | (q + 1) =>
      have hcard : #s ≤ q + 1 := by omega
      have IH := ih q ha' hcard
      have hmono : k ^ #s ≤ k ^ (q + 1) := Nat.pow_le_pow_right hk (by omega)
      set P := ∏ i ∈ s, a i with hP
      set Q := ∑ i ∈ s, (k - a i) with hQ
      set D := k - a j with hD
      have key1 : k ^ (#s + 1) = k ^ #s * D + k ^ #s * a j := by
        rw [← Nat.mul_add, hD, Nat.sub_add_cancel haj, pow_succ]
      have key2 : k ^ #s * D ≤ k ^ (q + 1) * D := Nat.mul_le_mul_right _ hmono
      have key3 : k ^ #s * a j ≤ (P + k ^ q * Q) * a j := Nat.mul_le_mul_right _ IH
      have key4 : (P + k ^ q * Q) * a j = a j * P + a j * (k ^ q * Q) := by ring
      have key5 : a j * (k ^ q * Q) ≤ k ^ (q + 1) * Q := by
        rw [pow_succ, Nat.mul_comm (k ^ q) k, Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ haj
      have key6 : k ^ (q + 1) * (D + Q) = k ^ (q + 1) * D + k ^ (q + 1) * Q := by ring
      omega

/-! ### Step 3: deficiencies are subadditive along edges

Write `δ(W) = k - |⋂_{v ∈ W} L v|` for the deficiency of a set of vertices.  Adjoining to `W` a
vertex `w` joined to some `v ∈ W` costs at most the deficiency of the edge `vw`, because
`⋂_W ⊆ L v` and intersecting with `L w` therefore discards at most `|L v \ L w|` colors.  Walking
along a spanning tree of each component then bounds the total deficiency of the components by the
total deficiency of the edges. -/

lemma listInter_singleton (L : ListAssignment V) (v : V) : listInter L {v} = L v := by
  ext a
  rw [mem_listInter ⟨v, Finset.mem_singleton_self v⟩]
  simp

lemma card_listInter_le {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {U : Finset V} (hU : U.Nonempty) : #(listInter L U) ≤ k := by
  obtain ⟨v, hv⟩ := hU
  rw [← hL v]
  exact Finset.card_le_card (listInter_subset hv)

/-- **Deficiency is subadditive along an edge.**  Adding to `U` a vertex `w` adjacent to some
`u ∈ U` increases the deficiency by at most the deficiency of the edge `uw`. -/
theorem sub_card_listInter_insert_le {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {U : Finset V} {u w : V} (hu : u ∈ U) :
    k - #(listInter L (insert w U)) ≤ (k - #(listInter L U)) + edgeDef L k s(u, w) := by
  have hU : U.Nonempty := ⟨u, hu⟩
  have hsub : listInter L U ⊆ L u := listInter_subset hu
  have h1 : #(listInter L U \ L w) + #(listInter L U ∩ L w) = #(listInter L U) :=
    Finset.card_sdiff_add_card_inter _ _
  have h2 : #(L u \ L w) + #(L u ∩ L w) = #(L u) := Finset.card_sdiff_add_card_inter _ _
  have h3 : #(listInter L U \ L w) ≤ #(L u \ L w) :=
    Finset.card_le_card (Finset.sdiff_subset_sdiff hsub (le_refl _))
  have h4 : #(listInter L U) ≤ k := card_listInter_le hL hU
  rw [listInter_insert L hU w, edgeDef_mk, hL u] at *
  omega

/-- The edges of `S` that lie inside the component `C`. -/
def compEdges (S : Finset (Sym2 V)) (C : (edgeGraph S).ConnectedComponent) : Finset (Sym2 V) :=
  S.filter (fun e => ∀ x : V, x ∈ e → x ∈ C.supp)

/-- The heart of Step 3: grow a connected set `U` of vertices of the component `C`, one boundary
edge at a time, keeping the running bound `δ(U) ≤ ∑_{e ∈ T} δ(e)` for a set `T` of edges lying
inside `U`.  The new edge is never already in `T`, because one of its ends is outside `U`. -/
private theorem grow_component {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    (S : Finset (Sym2 V)) (C : (edgeGraph S).ConnectedComponent) :
    ∀ (j : ℕ) (U : Finset V) (T : Finset (Sym2 V)), #(compFinset S C \ U) = j → U.Nonempty →
      U ⊆ compFinset S C → T ⊆ compEdges S C → (∀ e ∈ T, ∀ x : V, x ∈ e → x ∈ U) →
      k - #(listInter L U) ≤ ∑ e ∈ T, edgeDef L k e →
      k - #(compInter L S C) ≤ ∑ e ∈ compEdges S C, edgeDef L k e := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro U T hj hUne hUsub hTsub hTin hle
    rcases Finset.eq_empty_or_nonempty (compFinset S C \ U) with hd | ⟨w, hw⟩
    · have hUeq : U = compFinset S C :=
        Finset.Subset.antisymm hUsub (Finset.sdiff_eq_empty_iff_subset.mp hd)
      calc k - #(compInter L S C) = k - #(listInter L U) := by rw [hUeq, compInter]
        _ ≤ ∑ e ∈ T, edgeDef L k e := hle
        _ ≤ ∑ e ∈ compEdges S C, edgeDef L k e :=
            Finset.sum_le_sum_of_subset hTsub
    · obtain ⟨r, hr⟩ := hUne
      rw [Finset.mem_sdiff] at hw
      have hreach : (edgeGraph S).Reachable r w :=
        ConnectedComponent.exact
          ((mem_compFinset.mp (hUsub hr)).trans (mem_compFinset.mp hw.1).symm)
      obtain ⟨p⟩ := hreach
      obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (U : Set V) hr hw.2
      have hd1' : d.fst ∈ U := hd1
      have hd2' : d.snd ∉ U := hd2
      have hadj : (edgeGraph S).Adj d.fst d.snd := d.adj
      have hmem : d.edge ∈ S := by
        have := hadj
        rw [fromEdgeSet_adj] at this
        exact this.1
      have hsnd : (edgeGraph S).connectedComponentMk d.snd = C := by
        rw [← ConnectedComponent.connectedComponentMk_eq_of_adj hadj]
        exact mem_compFinset.mp (hUsub hd1')
      have hfst : (edgeGraph S).connectedComponentMk d.fst = C := mem_compFinset.mp (hUsub hd1')
      have hedge : d.edge ∈ compEdges S C := by
        rw [compEdges, Finset.mem_filter]
        refine ⟨hmem, fun x hx => ?_⟩
        rw [Dart.edge, Sym2.mem_iff] at hx
        rcases hx with rfl | rfl
        · exact hfst
        · exact hsnd
      have hnotT : d.edge ∉ T := fun hcon =>
        hd2' (hTin _ hcon d.snd (by rw [Dart.edge]; exact Sym2.mem_mk_right _ _))
      have hcard : #(compFinset S C \ insert d.snd U) < j := by
        rw [← hj]
        refine Finset.card_lt_card
          ⟨Finset.sdiff_subset_sdiff (le_refl _) (Finset.subset_insert _ _), fun hcon => ?_⟩
        have : d.snd ∈ compFinset S C \ U :=
          Finset.mem_sdiff.mpr ⟨mem_compFinset.mpr hsnd, hd2'⟩
        have := hcon this
        rw [Finset.mem_sdiff] at this
        exact this.2 (Finset.mem_insert_self _ _)
      refine ih _ hcard (insert d.snd U) (insert d.edge T) rfl ⟨d.snd, Finset.mem_insert_self _ _⟩
        ?_ ?_ ?_ ?_
      · exact Finset.insert_subset (mem_compFinset.mpr hsnd) hUsub
      · exact Finset.insert_subset hedge hTsub
      · intro e he x hx
        rw [Finset.mem_insert] at he
        rcases he with rfl | he
        · rw [Dart.edge, Sym2.mem_iff] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_insert_of_mem hd1'
          · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hTin e he x hx)
      · rw [Finset.sum_insert hnotT]
        have hstep : k - #(listInter L (insert d.snd U)) ≤
            (k - #(listInter L U)) + edgeDef L k s(d.fst, d.snd) :=
          sub_card_listInter_insert_le hL hd1'
        have : d.edge = s(d.fst, d.snd) := rfl
        rw [this]
        omega

/-- **Step 3, one component.**  The deficiency of a connected component is at most the total
deficiency of the edges lying inside it. -/
theorem sub_card_compInter_le {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    (S : Finset (Sym2 V)) (C : (edgeGraph S).ConnectedComponent) :
    k - #(compInter L S C) ≤ ∑ e ∈ compEdges S C, edgeDef L k e := by
  obtain ⟨r, hr⟩ := compFinset_nonempty S C
  refine grow_component hL S C _ {r} ∅ rfl ⟨r, Finset.mem_singleton_self r⟩ ?_ ?_ ?_ ?_
  · simpa using hr
  · exact Finset.empty_subset _
  · simp
  · rw [listInter_singleton, hL r]
    simp

/-- The edge sets of distinct components are disjoint, so summing the inner bounds of
`sub_card_compInter_le` over all components costs nothing. -/
theorem sum_sum_compEdges_le (L : ListAssignment V) (k : ℕ) (S : Finset (Sym2 V)) :
    ∑ C : (edgeGraph S).ConnectedComponent, ∑ e ∈ compEdges S C, edgeDef L k e
      ≤ ∑ e ∈ S, edgeDef L k e := by
  have hrw : ∀ C : (edgeGraph S).ConnectedComponent, ∑ e ∈ compEdges S C, edgeDef L k e
      = ∑ e ∈ S, if ∀ x : V, x ∈ e → x ∈ C.supp then edgeDef L k e else 0 :=
    fun C => Finset.sum_filter _ _
  rw [Finset.sum_congr rfl fun C _ => hrw C, Finset.sum_comm]
  refine Finset.sum_le_sum fun e _ => ?_
  have hcard : #{C : (edgeGraph S).ConnectedComponent | ∀ x : V, x ∈ e → x ∈ C.supp} ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ∈ (s(x, y) : Sym2 V) := Sym2.mem_mk_left x y
      exact (ha.2 x hx).symm.trans (hb.2 x hx)
  calc (∑ C : (edgeGraph S).ConnectedComponent,
        if ∀ x : V, x ∈ e → x ∈ C.supp then edgeDef L k e else 0)
      = #{C : (edgeGraph S).ConnectedComponent | ∀ x : V, x ∈ e → x ∈ C.supp} * edgeDef L k e := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    _ ≤ 1 * edgeDef L k e := Nat.mul_le_mul_right _ hcard
    _ = edgeDef L k e := one_mul _

/-- **Step 3.**  The total deficiency of the components of `(V, S)` is at most the total deficiency
of the edges of `S`. -/
theorem sum_sub_card_compInter_le {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    (S : Finset (Sym2 V)) :
    ∑ C : (edgeGraph S).ConnectedComponent, (k - #(compInter L S C)) ≤ ∑ e ∈ S, edgeDef L k e :=
  le_trans (Finset.sum_le_sum fun C _ => sub_card_compInter_le hL S C)
    (sum_sum_compEdges_le L k S)

lemma card_compInter_le {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    (S : Finset (Sym2 V)) (C : (edgeGraph S).ConnectedComponent) : #(compInter L S C) ≤ k :=
  card_listInter_le hL (compFinset_nonempty S C)

lemma listCount_le_pow {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    (S : Finset (Sym2 V)) : listCount L S ≤ k ^ compCount S := by
  rw [listCount_eq_prod]
  calc ∏ C : (edgeGraph S).ConnectedComponent, #(compInter L S C)
      ≤ ∏ _C : (edgeGraph S).ConnectedComponent, k := by
        gcongr with C
        exact card_compInter_le hL S C
    _ = k ^ compCount S := by rw [Finset.prod_const, Finset.card_univ, compCount]

/-! ### Counting the colorings that are constant on a single edge -/

/-- With `n = |V|`, exactly `|L u ∩ L v| · k ^ (n - 2)` of the colorings from a `k`-list
assignment give `u` and `v` the same color. -/
theorem listCount_singleton {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {u v : V} (huv : u ≠ v) :
    listCount L {s(u, v)} = #(L u ∩ L v) * k ^ (Fintype.card V - 2) := by
  classical
  have hset : {f ∈ Fintype.piFinset L | ∀ e ∈ ({s(u, v)} : Finset (Sym2 V)), ConstOnEdge f e}
      = {f ∈ Fintype.piFinset L | f u = f v} := by
    apply Finset.filter_congr
    intro f _
    simp
  have hfib : ∀ f ∈ {f ∈ Fintype.piFinset L | f u = f v}, f u ∈ L u ∩ L v := by
    intro f hf
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hf
    exact Finset.mem_inter.mpr ⟨hf.1 u, hf.2 ▸ hf.1 v⟩
  rw [listCount, hset, Finset.card_eq_sum_card_fiberwise hfib]
  have hone : ∀ a ∈ L u ∩ L v,
      #{f ∈ {f ∈ Fintype.piFinset L | f u = f v} | f u = a} = k ^ (Fintype.card V - 2) := by
    intro a ha
    rw [Finset.mem_inter] at ha
    have hEq : {f ∈ {f ∈ Fintype.piFinset L | f u = f v} | f u = a}
        = Fintype.piFinset (Function.update (Function.update L u {a}) v {a}) := by
      ext f
      simp only [Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · rintro ⟨⟨hf, hfuv⟩, hfa⟩ w
        rcases eq_or_ne w v with rfl | hwv
        · rw [Function.update_self, Finset.mem_singleton, ← hfuv, hfa]
        · rw [Function.update_of_ne hwv]
          rcases eq_or_ne w u with rfl | hwu
          · rw [Function.update_self, Finset.mem_singleton, hfa]
          · rw [Function.update_of_ne hwu]; exact hf w
      · intro hf
        have hfu : f u = a := by
          have := hf u
          rw [Function.update_of_ne huv, Function.update_self, Finset.mem_singleton] at this
          exact this
        have hfv : f v = a := by
          have := hf v
          rw [Function.update_self, Finset.mem_singleton] at this
          exact this
        refine ⟨⟨fun w => ?_, by rw [hfu, hfv]⟩, hfu⟩
        rcases eq_or_ne w v with rfl | hwv
        · rw [hfv]; exact ha.2
        rcases eq_or_ne w u with rfl | hwu
        · rw [hfu]; exact ha.1
        · have := hf w
          rwa [Function.update_of_ne hwv, Function.update_of_ne hwu] at this
    rw [hEq, Fintype.card_piFinset,
      ← Finset.prod_mul_prod_compl ({u, v} : Finset V) (fun w => #(Function.update
        (Function.update L u ({a} : Finset ℕ)) v ({a} : Finset ℕ) w))]
    have h1 : ∏ w ∈ ({u, v} : Finset V),
        #(Function.update (Function.update L u ({a} : Finset ℕ)) v ({a} : Finset ℕ) w) = 1 := by
      rw [Finset.prod_pair huv, Function.update_of_ne huv, Function.update_self,
        Function.update_self]
      simp
    have h2 : ∏ w ∈ ({u, v} : Finset V)ᶜ,
        #(Function.update (Function.update L u ({a} : Finset ℕ)) v ({a} : Finset ℕ) w)
          = k ^ (Fintype.card V - 2) := by
      rw [Finset.prod_congr rfl (g := fun _ => k) ?_, Finset.prod_const, Finset.card_compl,
        Finset.card_pair huv]
      intro w hw
      rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton] at hw
      push Not at hw
      rw [Function.update_of_ne hw.2, Function.update_of_ne hw.1]
      exact hL w
    rw [h1, h2, one_mul]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul]

/-- The exact value of the `S = {e}` term of the Whitney expansion: it is `k ^ (n-2)` times the
deficiency of the edge `e`. -/
theorem pow_sub_listCount_singleton {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    {p : ℕ} (hp : Fintype.card V = p + 3) {u v : V} (huv : u ≠ v) :
    (k : ℤ) ^ compCount {s(u, v)} - (listCount L {s(u, v)} : ℤ)
      = (k : ℤ) ^ (p + 1) * (edgeDef L k s(u, v) : ℤ) := by
  have hn : Fintype.card V - 2 = p + 1 := by omega
  have h1 : listCount L {s(u, v)} = #(L u ∩ L v) * k ^ (p + 1) := by
    rw [listCount_singleton hL huv, hn]
  have h2 : k ^ compCount ({s(u, v)} : Finset (Sym2 V)) = k * k ^ (p + 1) := by
    rw [← listCount_constList, listCount_singleton (isNListAssignment_constList k) huv, hn]
    simp
  have h3 : #(L u ∩ L v) ≤ k := by
    rw [← hL u]
    exact Finset.card_le_card Finset.inter_subset_left
  have h2' : (k : ℤ) ^ compCount ({s(u, v)} : Finset (Sym2 V)) = (k : ℤ) * (k : ℤ) ^ (p + 1) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h2
  rw [h1, h2', edgeDef_mk, Nat.cast_sub h3]
  push_cast
  ring

/-! ### Step 4: two edges already merge two independent pairs of vertices -/

/-- If a map identifies two independent pairs of points then its image misses at least two
points. -/
private theorem card_image_le_of_two_merges {W : Type*} [DecidableEq W] {q : V → W}
    {x₁ y₁ x₂ y₂ : V} (h₁ : q x₁ = q y₁) (h₂ : q x₂ = q y₂) (hy : y₁ ≠ y₂)
    (hx₁ : x₁ ≠ y₁) (hx₁' : x₁ ≠ y₂) (hx₂ : x₂ ≠ y₁) (hx₂' : x₂ ≠ y₂) :
    ∃ p, Fintype.card V = p + 3 ∧ #(Finset.univ.image q) ≤ p + 1 := by
  have h3 : 3 ≤ Fintype.card V := by
    have hcard : #({x₁, y₁, y₂} : Finset V) = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hx₁, hx₁']),
        Finset.card_insert_of_notMem (by simp [hy]), Finset.card_singleton]
    rw [← hcard, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  refine ⟨Fintype.card V - 3, by omega, ?_⟩
  have hsub : Finset.univ.image q ⊆ ((Finset.univ.erase y₁).erase y₂).image q := by
    intro c hc
    rw [Finset.mem_image] at hc ⊢
    obtain ⟨x, -, rfl⟩ := hc
    rcases eq_or_ne x y₁ with rfl | hxy₁
    · exact ⟨x₁, by simp [hx₁, hx₁'], h₁⟩
    rcases eq_or_ne x y₂ with rfl | hxy₂
    · exact ⟨x₂, by simp [hx₂, hx₂'], h₂⟩
    · exact ⟨x, by simp [hxy₁, hxy₂], rfl⟩
  have hcard2 : #((Finset.univ.erase y₁).erase y₂) = Fintype.card V - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hy.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  have := (Finset.card_le_card hsub).trans
    (Finset.card_image_le (s := (Finset.univ.erase y₁).erase y₂) (f := q))
  omega

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Step 4.**  Two distinct edges of a simple graph span at least three vertices and merge two
independent pairs, so the spanning subgraph they lie in has at most `n - 2` components. -/
theorem compCount_le_of_two_le {S : Finset (Sym2 V)} (hS : S ⊆ G.edgeFinset) (h2 : 2 ≤ #S) :
    ∃ p, Fintype.card V = p + 3 ∧ compCount S ≤ p + 1 := by
  classical
  obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := Finset.one_lt_card.mp h2
  induction e₁ using Sym2.ind with
  | _ a b =>
  induction e₂ using Sym2.ind with
  | _ c d =>
  set q : V → (edgeGraph S).ConnectedComponent := (edgeGraph S).connectedComponentMk with hq
  have hadj : ∀ {x y : V}, s(x, y) ∈ S → q x = q y := by
    intro x y hxy
    have hne' : x ≠ y := by
      have := hS hxy
      rw [mem_edgeFinset, mem_edgeSet] at this
      exact this.ne
    exact ConnectedComponent.connectedComponentMk_eq_of_adj
      ((fromEdgeSet_adj _).mpr ⟨hxy, hne'⟩)
  have hab : a ≠ b := by
    have := hS he₁; rw [mem_edgeFinset, mem_edgeSet] at this; exact this.ne
  have hcd : c ≠ d := by
    have := hS he₂; rw [mem_edgeFinset, mem_edgeSet] at this; exact this.ne
  have h1 : q a = q b := hadj he₁
  have h2' : q c = q d := hadj he₂
  have himg : compCount S = #(Finset.univ.image q) := by
    rw [compCount, hq, Finset.image_univ_of_surjective
      (fun C => C.ind fun v => ⟨v, rfl⟩), Finset.card_univ]
  rw [himg]
  rcases eq_or_ne a c with rfl | hac
  · have hbd : b ≠ d := fun h => hne (by rw [h])
    exact card_image_le_of_two_merges h1 h2' hbd hab hcd hab hcd
  rcases eq_or_ne a d with rfl | had
  · have hbc : b ≠ c := fun h => hne (by rw [h]; exact Sym2.eq_swap)
    exact card_image_le_of_two_merges h1 h2'.symm hbc hab hac hab hac
  rcases eq_or_ne b c with rfl | hbc
  · exact card_image_le_of_two_merges h1.symm h2' had hab.symm hcd hab.symm hcd
  rcases eq_or_ne b d with rfl | hbd
  · exact card_image_le_of_two_merges h1.symm h2'.symm hac hab.symm hbc hab.symm hbc
  · exact card_image_le_of_two_merges h1 h2' hbd hab had hbc.symm hcd

/-! ### Putting the four steps together -/

variable {G}

/-- The `S`-th term of the difference between the two Whitney expansions: the constant list beats
the list assignment `L` on the subset `S` by exactly this much. -/
def whitneyDefect (L : ListAssignment V) (k : ℕ) (S : Finset (Sym2 V)) : ℤ :=
  (k : ℤ) ^ compCount S - (listCount L S : ℤ)

lemma whitneyDefect_nonneg {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k)
    (S : Finset (Sym2 V)) : 0 ≤ whitneyDefect L k S := by
  rw [whitneyDefect, sub_nonneg]
  exact_mod_cast listCount_le_pow hL S

lemma whitneyDefect_empty {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k) :
    whitneyDefect L k ∅ = 0 := by
  have h1 : listCount L ∅ = k ^ Fintype.card V := by
    rw [listCount]
    have hfil : {f ∈ Fintype.piFinset L | ∀ e ∈ (∅ : Finset (Sym2 V)), ConstOnEdge f e}
        = Fintype.piFinset L := Finset.filter_true_of_mem (by simp)
    have hprod : ∏ v : V, #(L v) = ∏ _v : V, k := Finset.prod_congr rfl fun v _ => hL v
    rw [hfil, Fintype.card_piFinset, hprod, Finset.prod_const, Finset.card_univ]
  rw [whitneyDefect, h1, compCount_empty, Nat.cast_pow, sub_self]

/-- **Steps 2 and 3 combined.**  Away from the singletons, every term of the difference is at most
`k ^ p` times the total edge deficiency `t`. -/
lemma whitneyDefect_le {L : ListAssignment V} {k : ℕ} (hL : IsNListAssignment L k) (hk1 : 1 ≤ k)
    {p : ℕ} {S : Finset (Sym2 V)} (hcomp : compCount S ≤ p + 1) :
    whitneyDefect L k S ≤ (k : ℤ) ^ p * (∑ e ∈ S, edgeDef L k e : ℕ) := by
  classical
  have hstep2 : k ^ compCount S ≤ listCount L S
      + k ^ p * ∑ C : (edgeGraph S).ConnectedComponent, (k - #(compInter L S C)) := by
    rw [listCount_eq_prod]
    have h := pow_card_le_prod_add_pow_mul_sum hk1 (fun C => #(compInter L S C))
      (Finset.univ : Finset (edgeGraph S).ConnectedComponent) p
      (fun C _ => card_compInter_le hL S C) (by rw [Finset.card_univ]; exact hcomp)
    rwa [Finset.card_univ] at h
  have hstep3 : k ^ p * ∑ C : (edgeGraph S).ConnectedComponent, (k - #(compInter L S C))
      ≤ k ^ p * ∑ e ∈ S, edgeDef L k e :=
    Nat.mul_le_mul_left _ (sum_sub_card_compInter_le hL S)
  have hcast := (Nat.cast_le (α := ℤ)).mpr (hstep2.trans (Nat.add_le_add_left hstep3 _))
  rw [whitneyDefect]
  push_cast at hcast ⊢
  linarith

/-- **The Whitney expansions of the two counts, subtracted.** -/
theorem col_sub_colConst_eq (G : SimpleGraph V) [DecidableRel G.Adj] (L : ListAssignment V)
    (k : ℕ) : (G.col L : ℤ) - (G.colConst k : ℤ)
      = ∑ S ∈ G.edgeFinset.powerset, (-1) ^ (#S + 1) * whitneyDefect L k S := by
  rw [col_eq_sum_powerset G L, show G.colConst k = G.col (constList V k) from rfl,
    col_eq_sum_powerset G (constList V k), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [listCount_constList, whitneyDefect]
  push_cast
  ring

/-- **An explicit enumerative chromatic-choosability threshold.** If the number of colors exceeds
`2 ^ m`, where `m` is the number of edges, then `G` is enumeratively chromatic-choosable at `k`: no
`k`-list assignment has fewer colorings than the constant one.

The proof is inclusion–exclusion over the edge set.  In the difference of the two Whitney
expansions the `|S| = 1` terms contribute exactly `k ^ (n-2)` times the total edge deficiency `t`
(`pow_sub_listCount_singleton`), the `S = ∅` term contributes nothing, and every remaining term is
at most `k ^ (n-3) · t` in absolute value: two distinct edges already merge two independent pairs
of vertices, so `c(S) ≤ n - 2` (`compCount_le_of_two_le`), and Steps 2 and 3
(`pow_card_le_prod_add_pow_mul_sum`, `sum_sub_card_compInter_le`) bound the term by
`k ^ (c(S) - 1) · t`.  There are fewer than `2 ^ m` such terms, so `k > 2 ^ m` suffices.  No
connectivity hypothesis is needed: if `t = 0` the bound is `≥ 0` regardless.

This is far from sharp — Wang, Qian and Yan prove the same conclusion for
`k > (m - 1) / ln (1 + √2)`, using Whitney's broken cycle theorem, which Mathlib does not have. -/
theorem ecc_of_two_pow_lt {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 2 ^ #G.edgeFinset < k) : G.ECCAt k := by
  classical
  intro L hL
  have h2m : 1 ≤ 2 ^ #G.edgeFinset := Nat.one_le_two_pow
  have hk1 : 1 ≤ k := by omega
  set t : ℕ := ∑ e ∈ G.edgeFinset, edgeDef L k e with ht
  set P₁ : Finset (Finset (Sym2 V)) := G.edgeFinset.powerset.filter (fun S => #S = 1) with hP₁
  set P₂ : Finset (Finset (Sym2 V)) := G.edgeFinset.powerset.filter (fun S => ¬ #S = 1) with hP₂
  have hsplit : (∑ S ∈ P₁, (-1 : ℤ) ^ (#S + 1) * whitneyDefect L k S)
      + ∑ S ∈ P₂, (-1 : ℤ) ^ (#S + 1) * whitneyDefect L k S
      = ∑ S ∈ G.edgeFinset.powerset, (-1 : ℤ) ^ (#S + 1) * whitneyDefect L k S :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hone : (∑ S ∈ P₁, (-1 : ℤ) ^ (#S + 1) * whitneyDefect L k S)
      = ∑ S ∈ P₁, whitneyDefect L k S := by
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [hP₁, Finset.mem_filter] at hS
    rw [hS.2]
    norm_num
  have hrest : -(∑ S ∈ P₂, whitneyDefect L k S)
      ≤ ∑ S ∈ P₂, (-1 : ℤ) ^ (#S + 1) * whitneyDefect L k S := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun S _ => ?_
    rcases Nat.even_or_odd (#S + 1) with h | h
    · rw [h.neg_one_pow]; linarith [whitneyDefect_nonneg hL S]
    · rw [h.neg_one_pow]; linarith
  have hgoal : (0 : ℤ) ≤ (G.col L : ℤ) - (G.colConst k : ℤ) := by
    rw [col_sub_colConst_eq G L k, ← hsplit, hone]
    by_cases hm : 2 ≤ #G.edgeFinset
    · obtain ⟨p, hp, -⟩ := compCount_le_of_two_le G (Finset.Subset.refl _) hm
      -- the singleton terms, exactly
      have hsingle : (∑ S ∈ P₁, whitneyDefect L k S) = (k : ℤ) ^ (p + 1) * t := by
        have himg : P₁ = G.edgeFinset.image (fun e => ({e} : Finset (Sym2 V))) := by
          ext S
          simp only [hP₁, Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
          constructor
          · rintro ⟨hsub, hcard⟩
            obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp hcard
            exact ⟨e, hsub (Finset.mem_singleton_self e), rfl⟩
          · rintro ⟨e, he, rfl⟩
            exact ⟨Finset.singleton_subset_iff.mpr he, Finset.card_singleton e⟩
        rw [himg, Finset.sum_image (fun a _ b _ h => by simpa using h), ht, Nat.cast_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun e he => ?_
        induction e using Sym2.ind with
        | _ u v =>
          have huv : u ≠ v := by
            rw [mem_edgeFinset, mem_edgeSet] at he
            exact he.ne
          exact pow_sub_listCount_singleton hL hp huv
      -- everything else
      have hbound : (∑ S ∈ P₂, whitneyDefect L k S) ≤ 2 ^ #G.edgeFinset * ((k : ℤ) ^ p * t) := by
        have hb : ∀ S ∈ P₂, whitneyDefect L k S ≤ (k : ℤ) ^ p * t := by
          intro S hS
          rw [hP₂, Finset.mem_filter, Finset.mem_powerset] at hS
          have hnn : (0 : ℤ) ≤ (k : ℤ) ^ p * t := by positivity
          rcases Nat.lt_or_ge (#S) 2 with hlt | hge
          · have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
            rw [hS0, whitneyDefect_empty hL]
            exact hnn
          · obtain ⟨p', hp', hcomp⟩ := compCount_le_of_two_le G hS.1 hge
            have hpp : p' = p := by omega
            rw [hpp] at hcomp
            refine (whitneyDefect_le hL hk1 hcomp).trans ?_
            have : (∑ e ∈ S, edgeDef L k e : ℕ) ≤ (t : ℕ) :=
              Finset.sum_le_sum_of_subset hS.1
            have := (Nat.cast_le (α := ℤ)).mpr this
            have hkp : (0 : ℤ) ≤ (k : ℤ) ^ p := by positivity
            exact mul_le_mul_of_nonneg_left this hkp
        have hcardP₂ : (#P₂ : ℤ) ≤ 2 ^ #G.edgeFinset := by
          have : #P₂ ≤ #G.edgeFinset.powerset := Finset.card_filter_le _ _
          rw [Finset.card_powerset] at this
          exact_mod_cast this
        have hnn : (0 : ℤ) ≤ (k : ℤ) ^ p * t := by positivity
        calc (∑ S ∈ P₂, whitneyDefect L k S) ≤ #P₂ • ((k : ℤ) ^ p * t) :=
              Finset.sum_le_card_nsmul _ _ _ hb
          _ = (#P₂ : ℤ) * ((k : ℤ) ^ p * t) := by rw [nsmul_eq_mul]
          _ ≤ 2 ^ #G.edgeFinset * ((k : ℤ) ^ p * t) := mul_le_mul_of_nonneg_right hcardP₂ hnn
      have hkm : (2 : ℤ) ^ #G.edgeFinset ≤ (k : ℤ) := by exact_mod_cast hk.le
      have hnn : (0 : ℤ) ≤ (k : ℤ) ^ p * t := by positivity
      have hfin : (2 : ℤ) ^ #G.edgeFinset * ((k : ℤ) ^ p * t) ≤ (k : ℤ) ^ (p + 1) * t := by
        have hrw : (k : ℤ) ^ (p + 1) * t = (k : ℤ) * ((k : ℤ) ^ p * t) := by ring
        rw [hrw]
        exact mul_le_mul_of_nonneg_right hkm hnn
      linarith
    · -- at most one edge: every subset that is not a singleton is empty
      have hzero : (∑ S ∈ P₂, whitneyDefect L k S) = 0 := by
        refine Finset.sum_eq_zero fun S hS => ?_
        rw [hP₂, Finset.mem_filter, Finset.mem_powerset] at hS
        have : #S ≤ #G.edgeFinset := Finset.card_le_card hS.1
        have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
        rw [hS0, whitneyDefect_empty hL]
      have hpos : 0 ≤ ∑ S ∈ P₁, whitneyDefect L k S :=
        Finset.sum_nonneg fun S _ => whitneyDefect_nonneg hL S
      linarith
  have := (Nat.cast_le (α := ℤ)).mp (by linarith : (G.colConst k : ℤ) ≤ (G.col L : ℤ))
  exact this

/-- **Donner's theorem (1992).** Every graph is enumeratively chromatic-choosable at `k` for all
sufficiently large `k`: past some threshold the constant list assignment always minimizes the number
of colorings.

Donner's proof is by an algebraic-geometry / compactness argument and gives no bound.
`ecc_of_two_pow_lt` is an explicit form of the same statement, with the (very crude)
threshold `N = 2 ^ m + 1`, `m` the number of edges; Wang, Qian and Yan later brought the threshold
down to `(m - 1) / ln (1 + √2)`, which requires Whitney's broken cycle theorem. -/
theorem exists_ecc_forall_ge (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ N, ∀ k, N ≤ k → G.ECCAt k :=
  ⟨2 ^ #G.edgeFinset + 1, fun _ hk => ecc_of_two_pow_lt (by omega)⟩

/-! ### In the language of the list color function -/

/-- The threshold theorem stated as `P_ℓ(G, k) = P(G, k)`: past `2 ^ m` colors the list color
function agrees with the coloring count from a single palette. -/
theorem listColorFunction_eq_of_two_pow_lt {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 2 ^ #G.edgeFinset < k) : G.listColorFunction k = G.colConst k :=
  (ecc_iff_listColorFunction_eq k).mp (ecc_of_two_pow_lt hk)

/-- The same, against the genuine chromatic polynomial of `ListColoring.ChromaticPolynomial`: for
`k > 2 ^ m` the list color function of *any* graph is the evaluation of its chromatic polynomial.
This is the usual way the statement is phrased in the literature. -/
theorem listColorFunction_eq_eval_of_two_pow_lt {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 2 ^ #G.edgeFinset < k) :
    (G.listColorFunction k : ℤ) = (G.chromaticPolynomial).eval (k : ℤ) :=
  (ecc_iff_listColorFunction_eq_eval k).mp (ecc_of_two_pow_lt hk)

/-- Donner's theorem for the list color function. -/
theorem exists_listColorFunction_eq_forall_ge (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ N, ∀ k, N ≤ k → G.listColorFunction k = G.colConst k :=
  ⟨2 ^ #G.edgeFinset + 1, fun _ hk => listColorFunction_eq_of_two_pow_lt (by omega)⟩

end SimpleGraph

/-! ### Numerical checks -/

section Checks

open SimpleGraph Finset

/-- A triangle. -/
private abbrev T3 : SimpleGraph (Fin 3) := ⊤

private def L1 : ListAssignment (Fin 3) := ![{0, 1}, {1, 2}, {0, 2}]
private def L2 : ListAssignment (Fin 3) := ![{0, 1}, {0, 1}, {1, 2}]

-- the Whitney expansion of `col` on concrete list assignments
#guard (T3.col L1 : ℤ) =
  ∑ S ∈ T3.edgeFinset.powerset, (-1) ^ #S * (listCount L1 S : ℤ)
#guard (T3.col L2 : ℤ) =
  ∑ S ∈ T3.edgeFinset.powerset, (-1) ^ #S * (listCount L2 S : ℤ)

-- the product formula for `listCount`
#guard ∀ S ∈ T3.edgeFinset.powerset,
  listCount L1 S = ∏ C : (edgeGraph S).ConnectedComponent, #(compInter L1 S C)
#guard ∀ S ∈ T3.edgeFinset.powerset,
  listCount L2 S = ∏ C : (edgeGraph S).ConnectedComponent, #(compInter L2 S C)

/-- The path on three vertices. -/
private abbrev P3 : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun a b : Fin 3 => a.val + 1 = b.val

#guard (P3.col L1 : ℤ) = ∑ S ∈ P3.edgeFinset.powerset, (-1) ^ #S * (listCount L1 S : ℤ)
#guard ∀ S ∈ P3.edgeFinset.powerset,
  listCount L1 S = ∏ C : (edgeGraph S).ConnectedComponent, #(compInter L1 S C)

/-- `K₄`. -/
private abbrev K4 : SimpleGraph (Fin 4) := ⊤

private def L4 : ListAssignment (Fin 4) := ![{0, 1, 2}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}]

#guard (K4.col L4 : ℤ) = ∑ S ∈ K4.edgeFinset.powerset, (-1) ^ #S * (listCount L4 S : ℤ)
#guard ∀ S ∈ K4.edgeFinset.powerset,
  listCount L4 S = ∏ C : (edgeGraph S).ConnectedComponent, #(compInter L4 S C)

-- the exact value of the `|S| = 1` terms (`pow_sub_listCount_singleton`), here `n - 2 = 1`
-- for the triangle and `n - 2 = 2` for `K₄`
#guard listCount L1 {s(0, 1)} = #(L1 0 ∩ L1 1) * 2 ^ 1
#guard listCount L2 {s(1, 2)} = #(L2 1 ∩ L2 2) * 2 ^ 1
#guard listCount L4 {s(0, 2)} = #(L4 0 ∩ L4 2) * 3 ^ 2

-- Step 3: the total deficiency of the components is at most the total edge deficiency
#guard ∀ S ∈ T3.edgeFinset.powerset,
  (∑ C : (edgeGraph S).ConnectedComponent, (2 - #(compInter L1 S C))) ≤ ∑ e ∈ S, edgeDef L1 2 e
#guard ∀ S ∈ K4.edgeFinset.powerset,
  (∑ C : (edgeGraph S).ConnectedComponent, (3 - #(compInter L4 S C))) ≤ ∑ e ∈ S, edgeDef L4 3 e

-- Step 4: two edges leave at most `n - 2` components
#guard ∀ S ∈ K4.edgeFinset.powerset, 2 ≤ #S → compCount S ≤ 4 - 2

-- enumerative chromatic-choosability itself, on the same data: `col(G, L) ≥ col(G, k)`
#guard T3.colConst 2 ≤ T3.col L1
#guard T3.colConst 2 ≤ T3.col L2
#guard P3.colConst 2 ≤ P3.col L1
#guard K4.colConst 3 ≤ K4.col L4

/-- Three sliding windows of nine colors: a `9`-list assignment for the triangle, whose three
edges put the threshold of `ecc_of_two_pow_lt` at `2 ^ 3 = 8`. -/
private def L9 : ListAssignment (Fin 3) :=
  ![{0, 1, 2, 3, 4, 5, 6, 7, 8}, {2, 3, 4, 5, 6, 7, 8, 9, 10}, {4, 5, 6, 7, 8, 9, 10, 11, 12}]

-- above the threshold, as the theorem says: `504 = 9 · 8 · 7 ≤ 568`
#guard T3.colConst 9 = 504
#guard T3.col L9 = 568
#guard T3.colConst 9 ≤ T3.col L9

end Checks

#print axioms SimpleGraph.listCount_eq_prod
#print axioms SimpleGraph.col_eq_sum_powerset
#print axioms SimpleGraph.pow_card_le_prod_add_pow_mul_sum
#print axioms SimpleGraph.sub_card_listInter_insert_le
#print axioms SimpleGraph.sum_sub_card_compInter_le
#print axioms SimpleGraph.listCount_singleton
#print axioms SimpleGraph.pow_sub_listCount_singleton
#print axioms SimpleGraph.compCount_le_of_two_le
#print axioms SimpleGraph.col_sub_colConst_eq
#print axioms SimpleGraph.ecc_of_two_pow_lt
#print axioms SimpleGraph.exists_ecc_forall_ge
#print axioms SimpleGraph.listColorFunction_eq_of_two_pow_lt
#print axioms SimpleGraph.listColorFunction_eq_eval_of_two_pow_lt
#print axioms SimpleGraph.exists_listColorFunction_eq_forall_ge
