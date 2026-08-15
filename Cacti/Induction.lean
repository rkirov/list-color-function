/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.LeafPeeling
import Cacti.Absorb
import Cacti.Uniform
import Cacti.Bridge

/-!
# The block induction: statement and transport steps

The `k ≥ 4` cactus theorem (handoff §6, UM-107/108) is a strong induction on the vertex count
carrying the pair invariant: for pair-dominant weights, the weighted rooted profile is
pair-bounded by the uniform normalizer times the weight normalizers. This file packages the
transport steps the induction consumes.

* `rootedWcol_one` / `rootedWcol_const_at` — weight specializations;
* `rootedCol_pendant_uniform` — the uniform side of pendant absorption carries factor `k - 1`;
* `pendant_weight_dominant` — pendant absorption preserves pair-dominance with normalizer
  `(k-1) · W x · W u` (the bridge inequality, squared).
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

/-- **The pair-invariant induction** (UM-107/108, `k ≥ 4`): on a cactus with pair-dominant
weights, the weighted rooted profile is pair-bounded by the uniform normalizer times the
product of the weight normalizers.

Case structure: one-vertex base; pendant absorption away from the root; the bridge at the
root; and the cycle blocks (single cycle, and leaf-cycle absorption) — the last two are the
remaining open cases, tracked as the `UM-106`/`UM-107` formalization. -/
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
      · sorry

end MainInduction



end ListColoring
