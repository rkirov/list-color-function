/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.LeafPeeling
import Cacti.Absorb
import Cacti.Uniform
import Cacti.Bridge
import Cacti.CyclePair
import Cacti.CutVertex

/-!
# The block induction: statement and transport steps

The `k ≥ 4` cactus theorem (handoff §6, UM-107/108) is a strong induction on the vertex count
carrying the pair invariant: for pair-dominant weights, the weighted rooted profile is
pair-bounded by the uniform normalizer times the weight normalizers. This file packages the
transport steps the induction consumes, and runs the induction.

* `rootedWcol_one` / `rootedWcol_const_at` — weight specializations;
* `rootedCol_pendant_uniform` — the uniform side of pendant absorption carries factor `k - 1`;
* `pendant_weight_dominant` — pendant absorption preserves pair-dominance with normalizer
  `(k-1) · W x · W u` (the bridge inequality, squared);
* `rootedCol_absorb_uniform` — the uniform side of absorption at a cut vertex;
* `pair_bound_of_cut` — the cut-vertex step: the pair bound on both sides of a split gives the
  pair bound for the whole;
* `cactus_pair_bound` — the induction itself.

The structural dichotomy it rests on — a cactus with no pendant vertex is a single cycle, or
splits at a cut vertex — is `exists_cut_split_or_cyclic_index`, proved here from
`Cacti/CutVertex.lean` and `exists_iso_closePath_of_two_regular`. Nothing in this file is
proved outright, with no unproved step: the whole induction is complete.
-/

namespace ListColoring

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Trivial weights recover the rooted count. -/
theorem rootedWcol_one (L : ListAssignment V) (r : V) (c : ℕ) :
    rootedWcol G L (fun _ _ => 1) r c = rootedCol G L r c := by
  rw [rootedWcol, rootedCol]
  simp

/-- A weight constant at one vertex and trivial elsewhere extracts as a factor. -/
theorem rootedWcol_const_at (L : ListAssignment V) (u : V) (m : ℕ) (r : V) (c : ℕ) :
    rootedWcol G L (fun v _ => if v = u then m else 1) r c = m * rootedCol G L r c := by
  rw [rootedWcol, rootedCol, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [Finset.prod_ite_eq' Finset.univ u (fun _ => m)]
  simp

/-- **Pair-dominance is preserved by pendant absorption**: if the weights at `x` and at `u`
are pair-dominant on `k`-lists over `W x` and `W u`, the absorbed weight
`d ↦ w u d · ∑_{e ∈ L x, e ≠ d} w x e` is pair-dominant over `(k-1) · W x · W u`. -/
theorem pendant_weight_dominant {k : ℕ} (hk : 3 ≤ k) {Lx Lu : Finset ℕ}
    (hLx : Lx.card = k) {wx wu : ℕ → ℕ} {Wx Wu : ℕ}
    (hdx : ∀ c ∈ Lx, ∀ d ∈ Lx, c ≠ d → Wx ^ 2 ≤ wx c * wx d)
    (hdu : ∀ c ∈ Lu, ∀ d ∈ Lu, c ≠ d → Wu ^ 2 ≤ wu c * wu d) :
    ∀ c ∈ Lu, ∀ d ∈ Lu, c ≠ d →
      ((k - 1) * Wx * Wu) ^ 2 ≤
        (wu c * ∑ e ∈ Lx.filter (· ≠ c), wx e) * (wu d * ∑ e ∈ Lx.filter (· ≠ d), wx e) := by
  intro c hc d hd hcd
  have hsum : ∀ c', (k - 1) * Wx ≤ ∑ e ∈ Lx.filter (· ≠ c'), wx e := by
    intro c'
    by_cases hc' : c' ∈ Lx
    · have h := bridge_sum_ge hk hLx hdx hc'
      calc (k - 1) * Wx ≤ ∑ e ∈ Lx.erase c', wx e := h
        _ = ∑ e ∈ Lx.filter (· ≠ c'), wx e := by
            congr 1
            ext e
            simp [Finset.mem_erase, Finset.mem_filter, and_comm]
    · -- with `c' ∉ Lx` the filter contains any erase; the erase bound applies
      obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ ∈ Lx := Finset.card_pos.mp (by omega) |>.imp fun _ h => h
      calc (k - 1) * Wx ≤ ∑ e ∈ Lx.erase c₀, wx e := bridge_sum_ge hk hLx hdx hc₀
        _ ≤ ∑ e ∈ Lx.filter (· ≠ c'), wx e :=
            Finset.sum_le_sum_of_subset (fun e he => Finset.mem_filter.mpr
              ⟨Finset.mem_of_mem_erase he,
                fun heq => hc' (heq ▸ Finset.mem_of_mem_erase he)⟩)
  calc ((k - 1) * Wx * Wu) ^ 2
      = (Wu ^ 2) * (((k - 1) * Wx) * ((k - 1) * Wx)) := by ring
    _ ≤ (wu c * wu d) * ((∑ e ∈ Lx.filter (· ≠ c), wx e) * (∑ e ∈ Lx.filter (· ≠ d), wx e)) := by
        exact Nat.mul_le_mul (hdu c hc d hd hcd) (Nat.mul_le_mul (hsum c) (hsum d))
    _ = (wu c * ∑ e ∈ Lx.filter (· ≠ c), wx e) * (wu d * ∑ e ∈ Lx.filter (· ≠ d), wx e) := by
        ring


section PendantPrereqs

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Deleting a degree-one vertex of a cactus leaves a cactus. -/
theorem isCactus_induce_of_leaf {x : V} (hG : IsCactus G) (hdeg : G.degree x = 1)
    (hne : ∃ y : V, y ≠ x) : IsCactus (G.induce {y | y ≠ x}) := by
  refine ⟨connected_induce_of_degree_eq_one hG.1 hdeg hne, ?_⟩
  intro u v p q hp hq e hep heq
  have hp' : (p.map (induceVal G _)).IsCycle :=
    (Walk.isCycle_map_iff_of_injective induceVal_injective).mpr hp
  have hq' : (q.map (induceVal G _)).IsCycle :=
    (Walk.isCycle_map_iff_of_injective induceVal_injective).mpr hq
  have hep' : Sym2.map (induceVal G _) e ∈ (p.map (induceVal G _)).edges := by
    rw [Walk.edges_map]
    exact List.mem_map_of_mem hep
  have heq' : Sym2.map (induceVal G _) e ∈ (q.map (induceVal G _)).edges := by
    rw [Walk.edges_map]
    exact List.mem_map_of_mem heq
  have heqsets := hG.2 _ _ hp' hq' _ hep' heq'
  rw [edges_toFinset_map, edges_toFinset_map] at heqsets
  exact Finset.image_injective (Sym2.map.injective induceVal_injective) heqsets

/-- The uniform side of pendant absorption: the factor is exactly `k - 1`. -/
theorem rootedCol_pendant_uniform {x u : V} (hxu : G.Adj x u)
    (huniq : ∀ y, G.Adj x y → y = u) {r : V} (hrx : r ≠ x) {k : ℕ} (hk : 1 ≤ k) (c : ℕ) :
    rootedCol G (constList V k) r c =
      (k - 1) * rootedCol (G.induce {y | y ≠ x}) (fun v => constList V k v.val) ⟨r, hrx⟩ c := by
  have hu : u ∈ {y : V | y ≠ x} := hxu.ne'
  have h := rootedWcol_pendant (G := G) hxu huniq hrx (constList V k) (fun _ _ => 1) c
  rw [rootedWcol_one] at h
  rw [h]
  calc rootedWcol (G.induce {y | y ≠ x}) (fun v => constList V k v.val)
        (fun v d => if v.val = u then
            (fun _ => 1) d * ∑ e ∈ (constList V k x).filter (· ≠ d), (fun _ _ => 1) x e
          else (fun _ _ => 1) v.val d) ⟨r, hrx⟩ c
      = rootedWcol (G.induce {y | y ≠ x}) (fun v => constList V k v.val)
          (fun v _ => if v = (⟨u, hu⟩ : {y : V // y ≠ x}) then k - 1 else 1) ⟨r, hrx⟩ c := by
        refine rootedWcol_weight_congr (fun v d hd => ?_) _ _
        by_cases hvu : v.val = u
        · rw [if_pos hvu, if_pos (Subtype.ext hvu)]
          simp only [one_mul]
          rw [Finset.sum_const, smul_eq_mul, mul_one]
          have hd' : d ∈ Finset.range k := hd
          rw [show (constList V k x).filter (· ≠ d) = (Finset.range k).erase d from by
            ext e
            simp [Finset.mem_erase, Finset.mem_filter, and_comm, constList_apply]]
          rw [Finset.card_erase_of_mem hd', Finset.card_range]
        · rw [if_neg hvu, if_neg (fun h => hvu (congrArg Subtype.val h))]
    _ = (k - 1) * rootedCol (G.induce {y | y ≠ x}) (fun v => constList V k v.val)
          ⟨r, hrx⟩ c :=
        rootedWcol_const_at _ _ _ _ _

/-- The uniform side of absorption at a cut vertex: the `B`-side uniform count factors out,
since by colour symmetry it does not depend on the colour at the cut vertex. -/
theorem rootedCol_absorb_uniform {A B : Set V} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {u : V} (huA : u ∈ A) (huB : u ∈ B) (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hmeet : ∀ v, v ∈ A → v ∈ B → v = u)
    (hedge : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    {r : V} (hrA : r ∈ A) {k : ℕ} (hk : 1 ≤ k) (c : ℕ) :
    rootedCol G (constList V k) r c =
      rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
        rootedCol (G.induce A) (constList A k) ⟨r, hrA⟩ c := by
  have h := rootedWcol_absorb huA huB hcover hmeet hedge hrA (constList V k) (fun _ _ => 1) c
  rw [rootedWcol_one] at h
  rw [h]
  have hzero : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  calc rootedWcol (G.induce A) (fun v => constList V k v.val)
        (fun v d => if v.val = u then
            (1 : ℕ) * rootedWcol (G.induce B) (fun x => constList V k x.val)
              (fun x _ => if x.val = u then 1 else 1) ⟨u, huB⟩ d
          else 1) ⟨r, hrA⟩ c
      = rootedWcol (G.induce A) (fun v => constList V k v.val)
          (fun v _ => if v = (⟨u, huA⟩ : A) then
              rootedCol (G.induce B) (fun x => constList V k x.val) ⟨u, huB⟩ 0
            else 1) ⟨r, hrA⟩ c := by
        refine rootedWcol_weight_congr (fun v d hd => ?_) _ _
        by_cases hvu : v.val = u
        · rw [if_pos hvu, if_pos (Subtype.ext hvu), one_mul]
          rw [rootedWcol_weight_congr (fun _ _ _ => ite_self 1) _ _, rootedWcol_one]
          exact rootedCol_constList_eq (G.induce B) k ⟨u, huB⟩ hd hzero
        · rw [if_neg hvu, if_neg (fun hv => hvu (congrArg Subtype.val hv))]
    _ = _ := rootedWcol_const_at _ _ _ _ _

/-- **The cut-vertex step**: with `V` split at `u` into `A` and `B` and the root in `A`, the
pair bound on both sides gives the pair bound for `G`. The `B` side is absorbed into the weight
at `u`, where its uniform count times its normalizer product becomes the new normalizer. -/
theorem pair_bound_of_cut {A B : Set V} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {u : V} (huA : u ∈ A) (huB : u ∈ B) (hcover : ∀ v, v ∈ A ∨ v ∈ B)
    (hmeet : ∀ v, v ∈ A → v ∈ B → v = u)
    (hedge : ∀ x y, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    {r : V} (hrA : r ∈ A) {k : ℕ} (hk : 4 ≤ k)
    (L : ListAssignment V) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, ∀ c ∈ L v, ∀ d ∈ L v, c ≠ d → (W v) ^ 2 ≤ w v c * w v d)
    (hBside : ∀ (wB : B → ℕ → ℕ) (WB : B → ℕ),
      (∀ x, ∀ c ∈ L x.val, ∀ d ∈ L x.val, c ≠ d → (WB x) ^ 2 ≤ wB x c * wB x d) →
      ∀ c ∈ L u, ∀ d ∈ L u, c ≠ d →
        (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 * ∏ x, WB x) ^ 2 ≤
          rootedWcol (G.induce B) (fun x => L x.val) wB ⟨u, huB⟩ c *
            rootedWcol (G.induce B) (fun x => L x.val) wB ⟨u, huB⟩ d)
    (hAside : ∀ (wA : A → ℕ → ℕ) (WA : A → ℕ),
      (∀ v, ∀ c ∈ L v.val, ∀ d ∈ L v.val, c ≠ d → (WA v) ^ 2 ≤ wA v c * wA v d) →
      ∀ c ∈ L r, ∀ d ∈ L r, c ≠ d →
        (rootedCol (G.induce A) (constList A k) ⟨r, hrA⟩ 0 * ∏ v, WA v) ^ 2 ≤
          rootedWcol (G.induce A) (fun v => L v.val) wA ⟨r, hrA⟩ c *
            rootedWcol (G.induce A) (fun v => L v.val) wA ⟨r, hrA⟩ d) :
    ∀ c ∈ L r, ∀ d ∈ L r, c ≠ d →
      (rootedCol G (constList V k) r 0 * ∏ v, W v) ^ 2 ≤
        rootedWcol G L w r c * rootedWcol G L w r d := by
  intro c hc d hd hcd
  -- the `B` side, with `u`'s own weight charged to the `A` side
  have hB := hBside (fun x e => if x.val = u then 1 else w x.val e)
    (fun x => if x.val = u then 1 else W x.val) (by
      intro x c' hc' d' hd' hcd'
      by_cases hxu : x.val = u
      · rw [if_pos hxu, if_pos hxu, if_pos hxu]
        omega
      · rw [if_neg hxu, if_neg hxu, if_neg hxu]
        exact hdom x.val c' hc' d' hd' hcd')
  -- the absorbed weight at `u` is still pair-dominant, over the `B`-side normalizer
  have hA := hAside
    (fun v d' => if v.val = u then
        w u d' * rootedWcol (G.induce B) (fun x => L x.val)
          (fun x e => if x.val = u then 1 else w x.val e) ⟨u, huB⟩ d'
      else w v.val d')
    (fun v => if v.val = u then
        W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
          ∏ x : B, (if x.val = u then 1 else W x.val))
      else W v.val)
    (by
      intro v c' hc' d' hd' hcd'
      by_cases hvu : v.val = u
      · rw [if_pos hvu, if_pos hvu, if_pos hvu]
        have h1 := hdom u c' (hvu ▸ hc') d' (hvu ▸ hd') hcd'
        have h2 := hB c' (hvu ▸ hc') d' (hvu ▸ hd') hcd'
        calc (W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
                ∏ x : B, (if x.val = u then 1 else W x.val))) ^ 2
            = W u ^ 2 * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
                ∏ x : B, (if x.val = u then 1 else W x.val)) ^ 2 := by ring
          _ ≤ (w u c' * w u d') *
              (rootedWcol (G.induce B) (fun x => L x.val)
                  (fun x e => if x.val = u then 1 else w x.val e) ⟨u, huB⟩ c' *
                rootedWcol (G.induce B) (fun x => L x.val)
                  (fun x e => if x.val = u then 1 else w x.val e) ⟨u, huB⟩ d') :=
              Nat.mul_le_mul h1 h2
          _ = _ := by ring
      · rw [if_neg hvu, if_neg hvu, if_neg hvu]
        exact hdom v.val c' hc' d' hd' hcd') c hc d hd hcd
  -- rewrite the goal through absorption, then match the normalizer products
  rw [rootedWcol_absorb huA huB hcover hmeet hedge hrA L w c,
    rootedWcol_absorb huA huB hcover hmeet hedge hrA L w d,
    rootedCol_absorb_uniform huA huB hcover hmeet hedge hrA (by omega : 1 ≤ k) 0]
  have hWA : (∏ v : A, (if v.val = u then
        W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
          ∏ x : B, (if x.val = u then 1 else W x.val))
      else W v.val))
      = (W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
          ∏ x : B, (if x.val = u then 1 else W x.val))) *
        ∏ v ∈ Finset.univ.erase (⟨u, huA⟩ : A), W v.val := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨u, huA⟩ : A)), if_pos rfl]
    congr 1
    exact Finset.prod_congr rfl fun v hv =>
      if_neg (fun h => Finset.ne_of_mem_erase hv (Subtype.ext h))
  have hWAu : W u * ∏ v ∈ Finset.univ.erase (⟨u, huA⟩ : A), W v.val = ∏ v : A, W v.val :=
    Finset.mul_prod_erase Finset.univ (fun v : A => W v.val)
      (Finset.mem_univ (⟨u, huA⟩ : A))
  -- the whole normalizer product splits along the two sides
  have hAB : (∏ v, W v) = (∏ v : A, W v.val) * ∏ x : B, (if x.val = u then 1 else W x.val) := by
    have hA' : (∏ v : A, W v.val) = ∏ v ∈ A.toFinset, W v :=
      (Finset.prod_subtype A.toFinset (fun _ => Set.mem_toFinset) W).symm
    have hB' : (∏ x : B, (if x.val = u then 1 else W x.val))
        = ∏ x ∈ B.toFinset, (if x = u then 1 else W x) :=
      (Finset.prod_subtype B.toFinset (fun _ => Set.mem_toFinset)
        (fun x => if x = u then 1 else W x)).symm
    have huBF : u ∈ B.toFinset := Set.mem_toFinset.mpr huB
    have hBerase : (∏ x ∈ B.toFinset, (if x = u then 1 else W x))
        = ∏ x ∈ B.toFinset.erase u, W x := by
      rw [← Finset.mul_prod_erase B.toFinset (fun x => if x = u then 1 else W x) huBF,
        if_pos rfl, one_mul]
      exact Finset.prod_congr rfl fun x hx => if_neg (Finset.ne_of_mem_erase hx)
    have hdisj : Disjoint A.toFinset (B.toFinset.erase u) := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      exact Finset.ne_of_mem_erase hxB
        (hmeet x (Set.mem_toFinset.mp hxA)
          (Set.mem_toFinset.mp (Finset.mem_of_mem_erase hxB)))
    have huniv : (Finset.univ : Finset V) = A.toFinset ∪ B.toFinset.erase u := by
      refine (Finset.eq_univ_of_forall fun v => ?_).symm
      rcases hcover v with h | h
      · exact Finset.mem_union_left _ (Set.mem_toFinset.mpr h)
      · by_cases hvu : v = u
        · exact Finset.mem_union_left _ (Set.mem_toFinset.mpr (hvu ▸ huA))
        · exact Finset.mem_union_right _
            (Finset.mem_erase.mpr ⟨hvu, Set.mem_toFinset.mpr h⟩)
    rw [hA', hB', hBerase, ← Finset.prod_union hdisj]
    exact Finset.prod_congr huniv fun _ _ => rfl
  have hprod : rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
        rootedCol (G.induce A) (constList A k) ⟨r, hrA⟩ 0 * ∏ v, W v
      = rootedCol (G.induce A) (constList A k) ⟨r, hrA⟩ 0 *
        ∏ v : A, (if v.val = u then
            W u * (rootedCol (G.induce B) (constList B k) ⟨u, huB⟩ 0 *
              ∏ x : B, (if x.val = u then 1 else W x.val))
          else W v.val) := by
    rw [hWA, hAB, ← hWAu]
    ring
  rw [hprod]
  exact hA

end PendantPrereqs

section MainInduction

/-- Rooted weighted count of a one-vertex graph: the weight of the root's colour. -/
theorem rootedWcol_of_card_eq_one {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h1 : Fintype.card V = 1)
    (L : ListAssignment V) (w : V → ℕ → ℕ) (r : V) {c : ℕ} (hc : c ∈ L r) :
    rootedWcol G L w r c = w r c := by
  have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  rw [rootedWcol]
  have hset : (G.colorings L).filter (fun f => f r = c) = {fun _ => c} := by
    ext f
    simp only [Finset.mem_filter, SimpleGraph.mem_colorings_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hmem, hprop⟩, hr⟩
      funext v
      rw [Subsingleton.elim v r, hr]
    · rintro rfl
      refine ⟨⟨fun v => ?_, fun v u hadj => ?_⟩, rfl⟩
      · rw [Subsingleton.elim v r]; exact hc
      · exact absurd (Subsingleton.elim v u) hadj.ne
  rw [hset, Finset.sum_singleton]
  rw [show (Finset.univ : Finset V) = {r} from by
    ext v; simp [Subsingleton.elim v r]]
  rw [Finset.prod_singleton]

/-- **The structural dichotomy for cacti** (handoff §6.5): a cactus in which no vertex is
pendant either splits at a cut vertex into two smaller cacti, or is a single cycle — indexed
from any prescribed root.

With every degree at least two, a graph all of whose degrees are exactly two is a cycle
(`exists_iso_closePath_of_two_regular`), which the cyclic index reads off; otherwise some vertex
has degree at least three and `exists_cut_split_of_three_le_degree` splits the graph. -/
theorem exists_cut_split_or_cyclic_index {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : IsCactus G) (hdeg : ∀ v : V, 2 ≤ G.degree v)
    (r : V) :
    (∃ (u : V) (A B : Set V) (dA : DecidablePred (· ∈ A)) (dB : DecidablePred (· ∈ B)),
        letI := dA; letI := dB;
        (r ∈ A ∧ u ∈ A ∧ u ∈ B ∧
          (∀ v : V, v ∈ A ∨ v ∈ B) ∧ (∀ v : V, v ∈ A → v ∈ B → v = u) ∧
          (∀ x y : V, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B)) ∧
          (∃ a ∈ A, a ≠ u) ∧ (∃ b ∈ B, b ≠ u) ∧
          IsCactus (G.induce A) ∧ IsCactus (G.induce B))) ∨
      (∃ (m : ℕ) (ix : Fin (m + 1) ≃ V), 2 ≤ m ∧ ix 0 = r ∧
        ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1)) := by
  by_cases h3 : ∃ u : V, 3 ≤ G.degree u
  · obtain ⟨u, hu⟩ := h3
    exact Or.inl (exists_cut_split_of_three_le_degree hG hu r)
  · -- every degree is exactly two: the graph is a cycle, and the index rotates to the root
    push Not at h3
    have hdeg2 : ∀ v : V, G.degree v = 2 := fun v => by
      have h1 := h3 v
      have h2 := hdeg v
      omega
    obtain ⟨m, hm, ⟨e⟩⟩ := exists_iso_closePath_of_two_regular hG.1 hdeg2
    obtain ⟨ix, hix0, hadj⟩ := exists_cyclic_index hm e r
    exact Or.inr ⟨m, ix, hm, hix0, hadj⟩

/-- **The structural trichotomy** for a cactus on at least three vertices: it splits at a cut
vertex — the edge at a pendant vertex, or a genuine cut vertex — or it is a single cycle,
indexed from any prescribed root. This is the form the induction consumes when it does not
separate the pendant cases by hand. -/
theorem exists_cut_split_or_cyclic_index_of_three_le {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hG : IsCactus G) (hcard : 3 ≤ Fintype.card V)
    (r : V) :
    (∃ (u : V) (A B : Set V) (dA : DecidablePred (· ∈ A)) (dB : DecidablePred (· ∈ B)),
        letI := dA; letI := dB;
        (r ∈ A ∧ u ∈ A ∧ u ∈ B ∧
          (∀ v : V, v ∈ A ∨ v ∈ B) ∧ (∀ v : V, v ∈ A → v ∈ B → v = u) ∧
          (∀ x y : V, G.Adj x y → (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B)) ∧
          (∃ a ∈ A, a ≠ u) ∧ (∃ b ∈ B, b ≠ u) ∧
          IsCactus (G.induce A) ∧ IsCactus (G.induce B))) ∨
      (∃ (m : ℕ) (ix : Fin (m + 1) ≃ V), 2 ≤ m ∧ ix 0 = r ∧
        ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1)) := by
  by_cases hleaf : ∃ x : V, G.degree x = 1
  · obtain ⟨x, hx⟩ := hleaf
    exact Or.inl (exists_leaf_cut_split hG hx hcard r)
  · push Not at hleaf
    have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    refine exists_cut_split_or_cyclic_index hG (fun v => ?_) r
    have hpos : 0 < G.degree v := hG.1.preconnected.degree_pos_of_nontrivial v
    have h1 : G.degree v ≠ 1 := hleaf v
    omega

/-- **The pair-invariant induction** (UM-107/108, `k ≥ 4`): on a cactus with pair-dominant
weights, the weighted rooted profile is pair-bounded by the uniform normalizer times the
product of the weight normalizers.

Case structure: one-vertex base; pendant absorption away from the root; the bridge at the
root; and a cactus of minimum degree two, where `exists_cut_split_or_cyclic_index` either
splits at a cut vertex — `pair_bound_of_cut` and two uses of the induction hypothesis — or
presents the graph as a single cycle, closed by `cycle_pair_bound_index` (UM-106 + UM-107). -/
theorem cactus_pair_bound :
    ∀ (n : ℕ) (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → ∀ {k : ℕ}, 4 ≤ k → IsCactus G →
      ∀ (L : ListAssignment V), IsNListAssignment L k →
      ∀ (w : V → ℕ → ℕ) (W : V → ℕ),
        (∀ v, ∀ c ∈ L v, ∀ d ∈ L v, c ≠ d → (W v) ^ 2 ≤ w v c * w v d) →
      ∀ (r : V), ∀ c ∈ L r, ∀ d ∈ L r, c ≠ d →
        (rootedCol G (constList V k) r 0 * ∏ v, W v) ^ 2 ≤
          (rootedWcol G L w r c) * (rootedWcol G L w r d) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V _ _ G _ hcard k hk hG L hL w W hdom r c hc d hd hcd
    rcases Nat.lt_or_ge n 2 with hn | hn
    · -- base: at most one vertex (zero is impossible: `r` inhabits `V`)
      have h1 : Fintype.card V = 1 := by
        have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
        omega
      rw [rootedWcol_of_card_eq_one h1 L w r hc, rootedWcol_of_card_eq_one h1 L w r hd]
      have hA : rootedCol G (constList V k) r 0 = 1 := by
        have h0 : (0 : ℕ) ∈ constList V k r := by
          simp [constList_apply, Finset.mem_range]
          omega
        have h2 := rootedWcol_of_card_eq_one (G := G) h1 (constList V k) (fun _ _ => 1) r h0
        rw [rootedWcol_one] at h2
        exact h2
      haveI hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h1)
      have hprod : (∏ v, W v) = W r := by
        rw [show (Finset.univ : Finset V) = {r} from by
          ext v; simp [Subsingleton.elim v r]]
        rw [Finset.prod_singleton]
      rw [hA, hprod, one_mul]
      exact hdom r c hc d hd hcd
    · -- at least two vertices
      by_cases hpend : ∃ x, x ≠ r ∧ G.degree x = 1
      · -- a pendant vertex away from the root: absorb it
        obtain ⟨x, hxr, hdeg⟩ := hpend
        obtain ⟨u, hxu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
        have hux : u ≠ x := hxu.ne'
        have hrx : r ≠ x := hxr.symm
        -- the absorbed data on the complement of x
        have hG' : IsCactus (G.induce {y | y ≠ x}) :=
          isCactus_induce_of_leaf hG hdeg ⟨u, hux⟩
        have hL' : IsNListAssignment (fun v : {y : V // y ≠ x} => L v.val) k :=
          fun v => hL v.val
        have hdom' : ∀ v : {y : V // y ≠ x}, ∀ c' ∈ L v.val, ∀ d' ∈ L v.val, c' ≠ d' →
            ((if v.val = u then (k - 1) * W x * W u else W v.val)) ^ 2 ≤
              (if v.val = u then w u c' * ∑ e ∈ (L x).filter (· ≠ c'), w x e
                else w v.val c') *
              (if v.val = u then w u d' * ∑ e ∈ (L x).filter (· ≠ d'), w x e
                else w v.val d') := by
          intro v c' hc' d' hd' hcd'
          by_cases hvu : v.val = u
          · rw [if_pos hvu, if_pos hvu, if_pos hvu]
            exact pendant_weight_dominant (by omega) (hL x)
              (fun a ha b hb hab => hdom x a ha b hb hab)
              (fun a ha b hb hab => hdom u a ha b hb hab)
              c' (hvu ▸ hc') d' (hvu ▸ hd') hcd'
          · rw [if_neg hvu, if_neg hvu, if_neg hvu]
            exact hdom v.val c' hc' d' hd' hcd'
        have hcards : Fintype.card {y : V // y ≠ x} + 1 = n := by
          have hcong := Fintype.card_congr (delOptionEquiv x)
          rw [Fintype.card_option] at hcong
          omega
        have hIH := IH _ (by omega) {y : V // y ≠ x} (G.induce {y | y ≠ x}) rfl hk hG'
          _ hL' _ _ hdom' ⟨r, hrx⟩ c hc d hd hcd
        -- rewrite the goal through the pendant absorption
        rw [rootedWcol_pendant hxu huniq hrx L w c, rootedWcol_pendant hxu huniq hrx L w d,
          rootedCol_pendant_uniform hxu huniq hrx (by omega) 0]
        -- align the normalizers
        have hu' : (⟨u, hux⟩ : {y : V // y ≠ x}) ∈ (Finset.univ : Finset {y : V // y ≠ x}) :=
          Finset.mem_univ _
        have hprodV : (∏ v, W v) = W x * ∏ v : {y : V // y ≠ x}, W v.val := by
          rw [← Fintype.prod_equiv (delOptionEquiv x)
            (fun o => W ((delOptionEquiv x) o)) W (fun o => rfl)]
          rw [Fintype.prod_option]
          rfl
        have herase : (∏ v ∈ Finset.univ.erase (⟨u, hux⟩ : {y : V // y ≠ x}),
              (if v.val = u then (k - 1) * W x * W u else W v.val))
            = ∏ v ∈ Finset.univ.erase (⟨u, hux⟩ : {y : V // y ≠ x}), W v.val :=
          Finset.prod_congr rfl fun v hv =>
            if_neg (fun h => Finset.ne_of_mem_erase hv (Subtype.ext h))
        have hprodW' : (∏ v : {y : V // y ≠ x},
              (if v.val = u then (k - 1) * W x * W u else W v.val))
            = (k - 1) * W x * ∏ v : {y : V // y ≠ x}, W v.val := by
          rw [← Finset.mul_prod_erase Finset.univ _ hu', herase,
            ← Finset.mul_prod_erase Finset.univ (fun v => W v.val) hu']
          show (if (u : V) = u then (k - 1) * W x * W u else W u) * _ = _
          rw [if_pos rfl]
          ring
        calc ((k - 1) *
              rootedCol (G.induce {y | y ≠ x}) (fun v => constList V k v.val) ⟨r, hrx⟩ 0 *
              ∏ v, W v) ^ 2
            = (rootedCol (G.induce {y | y ≠ x}) (fun v => constList V k v.val) ⟨r, hrx⟩ 0 *
                ∏ v : {y : V // y ≠ x},
                  (if v.val = u then (k - 1) * W x * W u else W v.val)) ^ 2 := by
              rw [hprodV, hprodW']
              ring
          _ ≤ _ := hIH
      · -- no pendant away from the root
        by_cases hrdeg : G.degree r = 1
        · -- the root is a pendant: absorb everything beyond its neighbour
          obtain ⟨u, hru, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hrdeg
          have hur : u ≠ r := hru.ne'
          -- the shared absorption instance: A the edge, B the complement of r, cut at u
          have hcover : ∀ v : V, v ∈ ({r, u} : Set V) ∨ v ∈ {y : V | y ≠ r} := fun v => by
            by_cases hvr : v = r
            · exact Or.inl (Or.inl hvr)
            · exact Or.inr hvr
          have hmeet : ∀ v : V, v ∈ ({r, u} : Set V) → v ∈ {y : V | y ≠ r} → v = u := by
            intro v hvA hvB
            rcases hvA with h | h
            · exact absurd h hvB
            · exact h
          have hedge : ∀ x y, G.Adj x y →
              (x ∈ ({r, u} : Set V) ∧ y ∈ ({r, u} : Set V)) ∨
              (x ∈ {y : V | y ≠ r} ∧ y ∈ {y : V | y ≠ r}) := by
            intro a b hadj
            by_cases har : a = r
            · exact Or.inl ⟨Or.inl har, Or.inr (huniq b (har ▸ hadj))⟩
            · by_cases hbr : b = r
              · exact Or.inl ⟨Or.inr (huniq a (hbr ▸ hadj.symm)), Or.inl hbr⟩
              · exact Or.inr ⟨har, hbr⟩
          have hBedge : ∀ a b, G.Adj a b → a ∈ ({r, u} : Set V) → b ∈ ({r, u} : Set V) →
              (a = r ∧ b = u) ∨ (a = u ∧ b = r) := by
            intro a b hadj ha hb
            rcases ha with ha | ha <;> rcases hb with hb | hb
            · exact absurd (ha.symm ▸ hb.symm ▸ hadj) (G.irrefl)
            · exact Or.inl ⟨ha, hb⟩
            · exact Or.inr ⟨ha, hb⟩
            · exact absurd (ha.symm ▸ hb.symm ▸ hadj) (G.irrefl)
          -- IH data on the complement
          have hG' : IsCactus (G.induce {y | y ≠ r}) :=
            isCactus_induce_of_leaf hG hrdeg ⟨u, hur⟩
          have hL' : IsNListAssignment (fun v : {y : V // y ≠ r} => L v.val) k :=
            fun v => hL v.val
          have hcards : Fintype.card {y : V // y ≠ r} + 1 = n := by
            have hcong := Fintype.card_congr (delOptionEquiv r)
            rw [Fintype.card_option] at hcong
            omega
          have huB : u ∈ {y : V | y ≠ r} := hur
          -- the B-side weight and its dominance
          have hdomB : ∀ v : {y : V // y ≠ r}, ∀ c' ∈ L v.val, ∀ d' ∈ L v.val, c' ≠ d' →
              ((if v.val = u then 1 else W v.val)) ^ 2 ≤
                (if v.val = u then 1 else w v.val c') *
                (if v.val = u then 1 else w v.val d') := by
            intro v c' hc' d' hd' hcd'
            by_cases hvu : v.val = u
            · rw [if_pos hvu, if_pos hvu, if_pos hvu]
              omega
            · rw [if_neg hvu, if_neg hvu, if_neg hvu]
              exact hdom v.val c' hc' d' hd' hcd'
          have hIHB := IH _ (by omega) {y : V // y ≠ r} (G.induce {y | y ≠ r}) rfl hk hG'
            _ hL' (fun v e => if v.val = u then 1 else w v.val e)
            (fun v => if v.val = u then 1 else W v.val) hdomB ⟨u, huB⟩
          -- notation for the message and its normalizer
          set msg : ℕ → ℕ := fun e => rootedWcol (G.induce {y | y ≠ r})
            (fun v => L v.val) (fun v e' => if v.val = u then 1 else w v.val e')
            ⟨u, huB⟩ e with hmsg
          set N : ℕ := rootedCol (G.induce {y | y ≠ r})
            (constList {y : V // y ≠ r} k) ⟨u, huB⟩ 0 *
            ∏ v : {y : V // y ≠ r}, (if v.val = u then 1 else W v.val) with hN
          have hmsgdom : ∀ c' ∈ L u, ∀ d' ∈ L u, c' ≠ d' → N ^ 2 ≤ msg c' * msg d' :=
            fun c' hc' d' hd' hcd' => hIHB c' hc' d' hd' hcd'
          -- the profile through absorption and the edge
          have hxc : ∀ c'' ∈ L r, rootedWcol G L w r c'' =
              w r c'' * ∑ e ∈ (L u).filter (· ≠ c''), (w u e * msg e) := by
            intro c'' hc''
            rw [rootedWcol_absorb (A := ({r, u} : Set V)) (B := {y : V | y ≠ r}) (u := u)
              (Set.mem_insert_of_mem _ rfl) huB hcover hmeet hedge (Set.mem_insert _ _) L w c'']
            refine (rootedWcol_edge_full (G := G) (u := r) (x := u) hru hBedge L hc''
              _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)).trans ?_
            rw [if_neg (fun h : r = u => hur h.symm)]
            congr 1
            refine Finset.sum_congr rfl fun e he => ?_
            rw [if_pos rfl]
          -- composite dominance and the bridge sum
          have hωdom : ∀ c' ∈ L u, ∀ d' ∈ L u, c' ≠ d' →
              (W u * N) ^ 2 ≤ (w u c' * msg c') * (w u d' * msg d') := by
            intro c' hc' d' hd' hcd'
            calc (W u * N) ^ 2 = W u ^ 2 * N ^ 2 := by ring
              _ ≤ (w u c' * w u d') * (msg c' * msg d') :=
                  Nat.mul_le_mul (hdom u c' hc' d' hd' hcd') (hmsgdom c' hc' d' hd' hcd')
              _ = _ := by ring
          have hbridge : ∀ c', (k - 1) * (W u * N) ≤
              ∑ e ∈ (L u).filter (· ≠ c'), (w u e * msg e) := by
            intro c'
            by_cases hc' : c' ∈ L u
            · calc (k - 1) * (W u * N)
                  ≤ ∑ e ∈ (L u).erase c', (w u e * msg e) :=
                    bridge_sum_ge (by omega) (hL u) hωdom hc'
                _ = ∑ e ∈ (L u).filter (· ≠ c'), (w u e * msg e) := by
                    congr 1
                    ext e
                    simp [Finset.mem_erase, Finset.mem_filter, and_comm]
            · obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ ∈ L u := by
                have : 0 < (L u).card := by rw [hL u]; omega
                exact Finset.card_pos.mp this |>.imp fun _ h => h
              calc (k - 1) * (W u * N)
                  ≤ ∑ e ∈ (L u).erase c₀, (w u e * msg e) :=
                    bridge_sum_ge (by omega) (hL u) hωdom hc₀
                _ ≤ ∑ e ∈ (L u).filter (· ≠ c'), (w u e * msg e) :=
                    Finset.sum_le_sum_of_subset (fun e he => Finset.mem_filter.mpr
                      ⟨Finset.mem_of_mem_erase he,
                        fun heq => hc' (heq ▸ Finset.mem_of_mem_erase he)⟩)
          -- the uniform side
          have hmsgU : ∀ e ∈ Finset.range k,
              rootedCol (G.induce {y | y ≠ r}) (constList {y : V // y ≠ r} k) ⟨u, huB⟩ e
                = rootedCol (G.induce {y | y ≠ r}) (constList {y : V // y ≠ r} k)
                    ⟨u, huB⟩ 0 := by
            intro e he
            exact rootedCol_constList_eq _ k _ he (by simp [Finset.mem_range]; omega)
          have hAG : rootedCol G (constList V k) r 0 = (k - 1) *
              rootedCol (G.induce {y | y ≠ r}) (constList {y : V // y ≠ r} k) ⟨u, huB⟩ 0 := by
            have h0 : (0 : ℕ) ∈ constList V k r := by
              simp [constList_apply, Finset.mem_range]; omega
            have habs := rootedWcol_absorb (A := ({r, u} : Set V)) (B := {y : V | y ≠ r})
              (u := u) (Set.mem_insert_of_mem _ rfl) huB hcover hmeet hedge
              (Set.mem_insert _ _) (constList V k) (fun _ _ => 1) 0
            rw [rootedWcol_one] at habs
            rw [habs]
            refine (rootedWcol_edge_full (G := G) (u := r) (x := u) hru hBedge (constList V k)
              h0 _ (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)).trans ?_
            rw [if_neg (fun h : r = u => hur h.symm), one_mul]
            calc ∑ e ∈ (constList V k u).filter (· ≠ 0),
                  (if (u : V) = u then
                    (1 : ℕ) * rootedWcol (G.induce {y | y ≠ r})
                      (fun x' => constList V k x'.val)
                      (fun x' e' => if x'.val = u then 1 else 1) ⟨u, huB⟩ e
                  else 1)
                = ∑ e ∈ (constList V k u).filter (· ≠ 0),
                    rootedCol (G.induce {y | y ≠ r}) (constList {y : V // y ≠ r} k)
                      ⟨u, huB⟩ e := by
                  refine Finset.sum_congr rfl fun e he => ?_
                  rw [if_pos rfl, one_mul]
                  exact (rootedWcol_weight_congr (fun v d _ => ite_self _) _ _).trans
                    (rootedWcol_one _ _ _)
              _ = ∑ e ∈ (constList V k u).filter (· ≠ 0),
                    rootedCol (G.induce {y | y ≠ r}) (constList {y : V // y ≠ r} k)
                      ⟨u, huB⟩ 0 := by
                  refine Finset.sum_congr rfl fun e he => ?_
                  have he' : e ∈ Finset.range k := (Finset.mem_filter.mp he).1
                  exact hmsgU e he'
              _ = (k - 1) * rootedCol (G.induce {y | y ≠ r})
                    (constList {y : V // y ≠ r} k) ⟨u, huB⟩ 0 := by
                  rw [Finset.sum_const, smul_eq_mul]
                  congr 1
                  rw [show (constList V k u).filter (· ≠ (0:ℕ))
                      = (Finset.range k).erase 0 from by
                    ext e
                    simp [Finset.mem_erase, Finset.mem_filter, and_comm, constList_apply]]
                  rw [Finset.card_erase_of_mem (by simp [Finset.mem_range]; omega),
                    Finset.card_range]
          -- assemble
          rw [hxc c hc, hxc d hd, hAG]
          have hprodV : (∏ v, W v) = W r * ∏ v : {y : V // y ≠ r}, W v.val := by
            rw [← Fintype.prod_equiv (delOptionEquiv r)
              (fun o => W ((delOptionEquiv r) o)) W (fun o => rfl)]
            rw [Fintype.prod_option]
            rfl
          have huS : (⟨u, huB⟩ : {y : V // y ≠ r}) ∈
              (Finset.univ : Finset {y : V // y ≠ r}) := Finset.mem_univ _
          have herase : (∏ v ∈ Finset.univ.erase (⟨u, huB⟩ : {y : V // y ≠ r}),
                (if v.val = u then 1 else W v.val))
              = ∏ v ∈ Finset.univ.erase (⟨u, huB⟩ : {y : V // y ≠ r}), W v.val :=
            Finset.prod_congr rfl fun v hv =>
              if_neg (fun h => Finset.ne_of_mem_erase hv (Subtype.ext h))
          have hprodB : (∏ v : {y : V // y ≠ r}, W v.val)
              = W u * ∏ v : {y : V // y ≠ r}, (if v.val = u then 1 else W v.val) := by
            calc (∏ v : {y : V // y ≠ r}, W v.val)
                = W u * ∏ v ∈ Finset.univ.erase (⟨u, huB⟩ : {y : V // y ≠ r}), W v.val :=
                  (Finset.mul_prod_erase Finset.univ (fun v => W v.val) huS).symm
              _ = W u * ∏ v ∈ Finset.univ.erase (⟨u, huB⟩ : {y : V // y ≠ r}),
                    (if v.val = u then 1 else W v.val) := by rw [herase]
              _ = W u * ∏ v : {y : V // y ≠ r}, (if v.val = u then 1 else W v.val) := by
                  rw [← Finset.mul_prod_erase Finset.univ
                    (fun v => if v.val = u then 1 else W v.val) huS]
                  rw [show (if ((⟨u, huB⟩ : {y : V // y ≠ r}) : V) = u then (1:ℕ)
                      else W ((⟨u, huB⟩ : {y : V // y ≠ r}) : V)) = 1 from if_pos rfl]
                  rw [one_mul]
          calc ((k - 1) * rootedCol (G.induce {y | y ≠ r})
                (constList {y : V // y ≠ r} k) ⟨u, huB⟩ 0 * ∏ v, W v) ^ 2
              = (W r * ((k - 1) * (W u * N))) ^ 2 := by
                rw [hprodV, hprodB, hN]
                ring
            _ ≤ (W r * ∑ e ∈ (L u).filter (· ≠ c), (w u e * msg e)) *
                  (W r * ∑ e ∈ (L u).filter (· ≠ d), (w u e * msg e)) := by
                have h1 := hbridge c
                have h2 := hbridge d
                have h3 : (W r * ((k - 1) * (W u * N))) ^ 2
                    = (W r * ((k - 1) * (W u * N))) * (W r * ((k - 1) * (W u * N))) := sq _
                rw [h3]
                exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
            _ ≤ (w r c * ∑ e ∈ (L u).filter (· ≠ c), (w u e * msg e)) *
                  (w r d * ∑ e ∈ (L u).filter (· ≠ d), (w u e * msg e)) := by
                have hr2 := hdom r c hc d hd hcd
                calc (W r * ∑ e ∈ (L u).filter (· ≠ c), (w u e * msg e)) *
                      (W r * ∑ e ∈ (L u).filter (· ≠ d), (w u e * msg e))
                    = W r ^ 2 * ((∑ e ∈ (L u).filter (· ≠ c), (w u e * msg e)) *
                        (∑ e ∈ (L u).filter (· ≠ d), (w u e * msg e))) := by ring
                  _ ≤ (w r c * w r d) * ((∑ e ∈ (L u).filter (· ≠ c), (w u e * msg e)) *
                        (∑ e ∈ (L u).filter (· ≠ d), (w u e * msg e))) :=
                      Nat.mul_le_mul_right _ hr2
                  _ = _ := by ring
        · -- no pendant vertex anywhere: every vertex has degree at least two
          have hnt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
          have hdeg2 : ∀ v : V, 2 ≤ G.degree v := by
            intro v
            have hpos : 0 < G.degree v := hG.1.preconnected.degree_pos_of_nontrivial v
            by_cases hv : v = r
            · subst hv
              have h1 : G.degree v ≠ 1 := hrdeg
              omega
            · have h1 : G.degree v ≠ 1 := fun h => hpend ⟨v, hv, h⟩
              omega
          rcases exists_cut_split_or_cyclic_index hG hdeg2 r with
            ⟨u, A, B, dA, dB, hrA, huA, huB, hcover, hmeet, hedge, ⟨a, haA, hau⟩,
              ⟨b, hbB, hbu⟩, hcA, hcB⟩ | ⟨m, ix, hm, hix0, hadj⟩
          · -- a cut vertex: absorb the `B` side into the weight at `u`, recurse on both sides
            have hbA : b ∉ A := fun h => hbu (hmeet b h hbB)
            have haB : a ∉ B := fun h => hau (hmeet a haA h)
            refine pair_bound_of_cut huA huB hcover hmeet hedge hrA hk L w W hdom ?_ ?_
              c hc d hd hcd
            · intro wB WB hdomB c' hc' d' hd' hcd'
              exact IH _ (by rw [← hcard]; exact Fintype.card_subtype_lt (x := a) haB) _
                (G.induce B) rfl hk hcB _ (fun x => hL x.val) wB WB hdomB
                ⟨u, huB⟩ c' hc' d' hd' hcd'
            · intro wA WA hdomA c' hc' d' hd' hcd'
              exact IH _ (by rw [← hcard]; exact Fintype.card_subtype_lt (x := b) hbA) _
                (G.induce A) rfl hk hcA _ (fun v => hL v.val) wA WA hdomA
                ⟨r, hrA⟩ c' hc' d' hd' hcd'
          · -- a single cycle: the weighted cycle pair theorem closes it
            rw [← hix0] at hc hd ⊢
            exact cycle_pair_bound_index hm ix hadj hk L hL w W hdom c hc d hd hcd

end MainInduction



end ListColoring
