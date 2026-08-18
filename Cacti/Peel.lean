/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Absorb
import Cacti.LeafPeeling

/-!
# Weight peeling (UM-107)

The reduction of the weighted cycle pair bound to the bare one. Per weighted vertex, the
two-valued domination and the extension-count slack `k - 3 ≥ 1` let the weight be peeled to a
constant, extracting its normalizer squared from the pair.

The heart is pure algebra: for `a ≤ b` with `B·B' ≤ C·C'`,
`(a·B + b·C)(a·B' + b·C') ≥ a·b·(B + C)(B' + C')` — the difference is
`(b - a)(b·C·C' - a·B·B')`, a product of nonnegatives.

* `peel_algebra` — that inequality, in `ℕ`;
* `rootedWcol_eq_sum_slices` — the fibrewise decomposition over a chosen vertex's colour;
* the extension-count bounds and the peel induction follow.
-/

namespace ListColoring

open SimpleGraph Finset

/-- **The peel algebra**: for `a ≤ b` and `B·B' ≤ C·C'`,
`(a·B + b·C)·(a·B' + b·C') ≥ a·b·(B + C)·(B' + C')`. -/
theorem peel_algebra {a b B B' C C' : ℕ} (hab : a ≤ b) (hBC : B * B' ≤ C * C') :
    a * b * ((B + C) * (B' + C')) ≤ (a * B + b * C) * (a * B' + b * C') := by
  have hkey : a * b * ((B + C) * (B' + C')) + (b - a) * (b * (C * C') - a * (B * B'))
      = (a * B + b * C) * (a * B' + b * C') := by
    have h1 : a * (B * B') ≤ b * (C * C') :=
      Nat.mul_le_mul hab hBC
    zify [hab, hBC, h1]
    ring
  omega

/-- The **doubly rooted count**: colorings fixing the colours of two vertices. -/
def rootedWcol2 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (L : ListAssignment V) (w : V → ℕ → ℕ) (r : V) (c : ℕ)
    (u : V) (a : ℕ) : ℕ :=
  ∑ f ∈ (G.colorings L).filter (fun f => f r = c ∧ f u = a), ∏ v, w v (f v)

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The rooted count decomposes over the colour of any second vertex. -/
theorem rootedWcol_eq_sum_rootedWcol2 (L : ListAssignment V) (w : V → ℕ → ℕ)
    (r : V) (c : ℕ) (u : V) :
    rootedWcol G L w r c = ∑ a ∈ L u, rootedWcol2 G L w r c u a := by
  rw [rootedWcol]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun f => f u)
    (fun f hf => G.mem_list_of_mem_colorings (Finset.mem_filter.mp hf).1 u)
    (fun f => ∏ v, w v (f v))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rootedWcol2]
  congr 1
  ext f
  simp only [Finset.mem_filter]
  tauto

/-- Slices are monotone in the weight at the sliced vertex: changing `w u` only rescales each
slice by the value at its colour. -/
theorem rootedWcol2_weight_at (L : ListAssignment V) (w : V → ℕ → ℕ) (r : V) (c : ℕ)
    (u : V) (a : ℕ) (hru : r ≠ u) :
    rootedWcol2 G L w r c u a
      = w u a * rootedWcol2 G L (fun v e => if v = u then 1 else w v e) r c u a := by
  rw [rootedWcol2, rootedWcol2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [Finset.mem_filter] at hf
  have hu' : (u : V) ∈ (Finset.univ : Finset V) := Finset.mem_univ _
  rw [← Finset.mul_prod_erase Finset.univ (fun v => w v (f v)) hu',
    ← Finset.mul_prod_erase Finset.univ
      (fun v => (if v = u then 1 else w v (f v))) hu']
  rw [if_pos rfl, one_mul, hf.2.2]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [if_neg (Finset.ne_of_mem_erase hv)]


/-- **The peel step** (UM-107's engine): at a vertex `u ≠ r` whose weight is pair-dominant
over `W u`, if every bare slice is dominated by the sum of the others (the extension-count
slack), then trivializing the weight at `u` extracts `(W u)²` from the pair. -/
theorem peel_step (L : ListAssignment V) (w : V → ℕ → ℕ) {r u : V} (hru : r ≠ u)
    {k : ℕ} (hk : 4 ≤ k) (hLu : (L u).card = k) {Wu : ℕ}
    (hdom : ∀ c ∈ L u, ∀ d ∈ L u, c ≠ d → Wu ^ 2 ≤ w u c * w u d)
    {c d : ℕ}
    (hslack : ∀ a ∈ L u, ∀ c' ∈ ({c, d} : Finset ℕ),
      rootedWcol2 G L (fun v e => if v = u then 1 else w v e) r c' u a ≤
        ∑ e ∈ (L u).erase a,
          rootedWcol2 G L (fun v e => if v = u then 1 else w v e) r c' u e) :
    Wu ^ 2 * (rootedWcol G L (fun v e => if v = u then 1 else w v e) r c *
        rootedWcol G L (fun v e => if v = u then 1 else w v e) r d) ≤
      rootedWcol G L w r c * rootedWcol G L w r d := by
  set w' : V → ℕ → ℕ := fun v e => if v = u then 1 else w v e with hw'
  -- the weighted profile as a slice sum
  have hslice : ∀ c', rootedWcol G L w r c'
      = ∑ a ∈ L u, w u a * rootedWcol2 G L w' r c' u a := by
    intro c'
    rw [rootedWcol_eq_sum_rootedWcol2 L w r c' u]
    exact Finset.sum_congr rfl fun a _ => rootedWcol2_weight_at L w r c' u a hru
  have hslice' : ∀ c', rootedWcol G L w' r c'
      = ∑ a ∈ L u, rootedWcol2 G L w' r c' u a := fun c' =>
    rootedWcol_eq_sum_rootedWcol2 L w' r c' u
  by_cases hW0 : Wu = 0
  · rw [hW0]
    simp
  have hWpos : 0 < Wu := Nat.pos_of_ne_zero hW0
  by_cases hdef : ∃ a ∈ L u, w u a < Wu
  · -- a deficient colour: two-valued lower bound and the peel algebra
    obtain ⟨a, ha, haW⟩ := hdef
    have hLerase : ((L u).erase a).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem ha, hLu]
      omega
    obtain ⟨e₀, he₀, hm⟩ := Finset.exists_min_image _ (w u) hLerase
    set m := w u e₀ with hmdef
    have hma : Wu ^ 2 ≤ w u a * m :=
      hdom a ha e₀ (Finset.mem_of_mem_erase he₀) (fun h => Finset.ne_of_mem_erase he₀ h.symm)
        |>.trans (le_of_eq rfl)
    have ham : w u a ≤ m := by
      by_contra hcon
      push Not at hcon
      have hmW : m < Wu := lt_trans hcon haW
      have h1 : w u a * m < Wu * Wu :=
        Nat.mul_lt_mul_of_lt_of_le haW (le_of_lt hmW) hWpos
      rw [pow_two] at hma
      omega
    -- the two-valued lower bound on each profile
    have hlow : ∀ c', w u a * rootedWcol2 G L w' r c' u a +
        m * ∑ e ∈ (L u).erase a, rootedWcol2 G L w' r c' u e ≤
          rootedWcol G L w r c' := by
      intro c'
      rw [hslice c', ← Finset.add_sum_erase _ _ ha]
      refine Nat.add_le_add_left ?_ _
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun e he => ?_
      exact Nat.mul_le_mul_right _ (hm e he)
    -- apply the peel algebra with B the a-slice and C the rest
    have halg := peel_algebra (a := w u a) (b := m)
      (B := rootedWcol2 G L w' r c u a)
      (B' := rootedWcol2 G L w' r d u a)
      (C := ∑ e ∈ (L u).erase a, rootedWcol2 G L w' r c u e)
      (C' := ∑ e ∈ (L u).erase a, rootedWcol2 G L w' r d u e)
      ham
      (Nat.mul_le_mul (hslack a ha c (Finset.mem_insert_self _ _))
        (hslack a ha d (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
    calc Wu ^ 2 * (rootedWcol G L w' r c * rootedWcol G L w' r d)
        = Wu ^ 2 * ((∑ e ∈ L u, rootedWcol2 G L w' r c u e) *
            (∑ e ∈ L u, rootedWcol2 G L w' r d u e)) := by rw [hslice' c, hslice' d]
      _ = Wu ^ 2 * (((rootedWcol2 G L w' r c u a) +
            ∑ e ∈ (L u).erase a, rootedWcol2 G L w' r c u e) *
            ((rootedWcol2 G L w' r d u a) +
            ∑ e ∈ (L u).erase a, rootedWcol2 G L w' r d u e)) := by
          rw [Finset.add_sum_erase _ _ ha, Finset.add_sum_erase _ _ ha]
      _ ≤ (w u a * m) * (((rootedWcol2 G L w' r c u a) +
            ∑ e ∈ (L u).erase a, rootedWcol2 G L w' r c u e) *
            ((rootedWcol2 G L w' r d u a) +
            ∑ e ∈ (L u).erase a, rootedWcol2 G L w' r d u e)) :=
          Nat.mul_le_mul_right _ (by rw [pow_two] at hma ⊢; exact hma)
      _ ≤ (w u a * rootedWcol2 G L w' r c u a +
            m * ∑ e ∈ (L u).erase a, rootedWcol2 G L w' r c u e) *
          (w u a * rootedWcol2 G L w' r d u a +
            m * ∑ e ∈ (L u).erase a, rootedWcol2 G L w' r d u e) := halg
      _ ≤ rootedWcol G L w r c * rootedWcol G L w r d :=
          Nat.mul_le_mul (hlow c) (hlow d)
  · -- no deficient colour: every weight clears `Wu`
    push Not at hdef
    have hlow : ∀ c', Wu * rootedWcol G L w' r c' ≤ rootedWcol G L w r c' := by
      intro c'
      rw [hslice c', hslice' c', Finset.mul_sum]
      refine Finset.sum_le_sum fun e he => ?_
      exact Nat.mul_le_mul_right _ (hdef e he)
    calc Wu ^ 2 * (rootedWcol G L w' r c * rootedWcol G L w' r d)
        = (Wu * rootedWcol G L w' r c) * (Wu * rootedWcol G L w' r d) := by ring
      _ ≤ rootedWcol G L w r c * rootedWcol G L w r d :=
          Nat.mul_le_mul (hlow c) (hlow d)



section Deletion

/-- Splitting a product over all vertices at one vertex. -/
theorem prod_delOption (F : V → ℕ) (u : V) :
    (∏ v, F v) = F u * ∏ v : {y : V // y ≠ u}, F v.val := by
  rw [← Fintype.prod_equiv (delOptionEquiv u)
    (fun o => F ((delOptionEquiv u) o)) F (fun o => rfl)]
  rw [Fintype.prod_option]
  rfl

/-- **Vertex deletion**: with the weight trivial at `u`, the doubly rooted count is the sum
over colorings of the complement compatible with `a` at `u`. -/
theorem rootedWcol2_delete {r u : V} (hru : r ≠ u) (L : ListAssignment V) (w : V → ℕ → ℕ)
    (c a : ℕ) (ha : a ∈ L u) :
    rootedWcol2 G L (fun v e => if v = u then 1 else w v e) r c u a
      = ∑ g ∈ ((G.induce {y | y ≠ u}).colorings (fun v => L v.val)).filter
          (fun g => g ⟨r, hru⟩ = c ∧ ∀ y : {y : V // y ≠ u}, G.Adj u y.val → g y ≠ a),
          ∏ v : {y : V // y ≠ u}, w v.val (g v) := by
  rw [rootedWcol2]
  refine Finset.sum_nbij' (fun f => fun v => f v.val)
    (fun g => fun v => if hv : v = u then a else g ⟨v, hv⟩) ?_ ?_ ?_ ?_ ?_
  · -- forward membership
    intro f hf
    rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff] at hf
    obtain ⟨⟨hmem, hprop⟩, hfr, hfu⟩ := hf
    rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff]
    exact ⟨⟨fun v => hmem v.val, fun v y hadj => hprop v.val y.val hadj⟩, hfr,
      fun y hadj h => hprop u y.val hadj (hfu.trans (h.symm : a = f y.val))⟩
  · -- backward membership
    intro g hg
    rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff] at hg
    obtain ⟨⟨hmem, hprop⟩, hgr, hcompat⟩ := hg
    rw [Finset.mem_filter, SimpleGraph.mem_colorings_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro v
      by_cases hv : v = u
      · rw [dif_pos hv, hv]
        exact ha
      · rw [dif_neg hv]
        exact hmem _
    · intro v y hadj
      by_cases hv : v = u
      · rw [dif_pos hv]
        by_cases hy : y = u
        · exact absurd (hv ▸ hy ▸ hadj) (G.irrefl)
        · rw [dif_neg hy]
          exact fun h => hcompat ⟨y, hy⟩ (hv ▸ hadj) h.symm
      · rw [dif_neg hv]
        by_cases hy : y = u
        · rw [dif_pos hy]
          exact fun h => hcompat ⟨v, hv⟩ (hy ▸ hadj.symm) h
        · rw [dif_neg hy]
          exact hprop ⟨v, hv⟩ ⟨y, hy⟩ hadj
    · show (if hv : r = u then a else g ⟨r, hv⟩) = c
      rw [dif_neg hru]
      exact hgr
    · show (if hv : u = u then a else g ⟨u, hv⟩) = a
      rw [dif_pos rfl]
  · -- left inverse
    intro f hf
    rw [Finset.mem_filter] at hf
    funext v
    show (if hv : v = u then a else f v) = f v
    by_cases hv : v = u
    · rw [dif_pos hv, ← hf.2.2, hv]
    · rw [dif_neg hv]
  · -- right inverse
    intro g hg
    funext v
    show (if hv : (v : V) = u then a else g ⟨v, hv⟩) = g v
    rw [dif_neg v.property]
  · -- summand
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [prod_delOption (fun v => if v = u then 1 else w v (f v)) u, if_pos rfl, one_mul]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [if_neg v.property]

end Deletion

section Slack

set_option maxHeartbeats 1600000 in
/-- **The extension-count slack**: at a vertex with at most two neighbours carrying a `k`-list,
`k ≥ 4`, every bare slice is dominated by the sum of the others. -/
theorem slack_of_two_nbrs {r u : V} (hru : r ≠ u) {n₁ n₂ : V}
    (hnbrs : ∀ y, G.Adj u y → y = n₁ ∨ y = n₂)
    {k : ℕ} (hk : 4 ≤ k) (L : ListAssignment V) (hLu : (L u).card = k)
    (w : V → ℕ → ℕ) (c' : ℕ) :
    ∀ a ∈ L u,
      rootedWcol2 G L (fun v e => if v = u then 1 else w v e) r c' u a ≤
        ∑ e ∈ (L u).erase a,
          rootedWcol2 G L (fun v e => if v = u then 1 else w v e) r c' u e := by
  intro a ha
  rw [rootedWcol2_delete hru L w c' a ha]
  have hrw : ∀ e ∈ (L u).erase a,
      rootedWcol2 G L (fun v e' => if v = u then 1 else w v e') r c' u e
        = ∑ g ∈ ((G.induce {y | y ≠ u}).colorings (fun v => L v.val)).filter
            (fun g => g ⟨r, hru⟩ = c' ∧ ∀ y : {y : V // y ≠ u}, G.Adj u y.val → g y ≠ e),
            ∏ v : {y : V // y ≠ u}, w v.val (g v) := fun e he =>
    rootedWcol2_delete hru L w c' e (Finset.mem_of_mem_erase he)
  rw [Finset.sum_congr rfl hrw]
  -- rewrite both sides as indicator sums over the root-filtered base set
  have hsplit : ∀ b : ℕ,
      (∑ g ∈ ((G.induce {y | y ≠ u}).colorings (fun v => L v.val)).filter
          (fun g => g ⟨r, hru⟩ = c' ∧ ∀ y : {y : V // y ≠ u}, G.Adj u y.val → g y ≠ b),
          ∏ v : {y : V // y ≠ u}, w v.val (g v))
        = ∑ g ∈ ((G.induce {y | y ≠ u}).colorings (fun v => L v.val)).filter
            (fun g => g ⟨r, hru⟩ = c'),
            (if (∀ y : {y : V // y ≠ u}, G.Adj u y.val → g y ≠ b) then
              ∏ v : {y : V // y ≠ u}, w v.val (g v) else 0) := by
    intro b
    rw [← Finset.sum_filter, Finset.filter_filter]
  rw [hsplit a, Finset.sum_congr rfl (fun e he => hsplit e), Finset.sum_comm]
  refine Finset.sum_le_sum fun g hg => ?_
  by_cases hcompat : ∀ y : {y : V // y ≠ u}, G.Adj u y.val → g y ≠ a
  · rw [if_pos hcompat]
    -- the excluded colour values: the image of `g` on the ≤ 2 neighbours of `u`
    set D : Finset ℕ :=
      (Finset.univ.filter (fun y : {y : V // y ≠ u} => G.Adj u y.val)).image g with hD
    have hDcard : D.card ≤ 2 := by
      have h1 : (Finset.univ.filter (fun y : {y : V // y ≠ u} => G.Adj u y.val)).card
          = ((Finset.univ.filter
              (fun y : {y : V // y ≠ u} => G.Adj u y.val)).image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      have h2 : ((Finset.univ.filter
          (fun y : {y : V // y ≠ u} => G.Adj u y.val)).image Subtype.val)
          ⊆ ({n₁, n₂} : Finset V) := by
        intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨y, hy, rfl⟩ := hv
        rw [Finset.mem_filter] at hy
        rcases hnbrs y.val hy.2 with h | h
        · exact Finset.mem_insert.mpr (Or.inl h)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
      calc D.card ≤ (Finset.univ.filter
            (fun y : {y : V // y ≠ u} => G.Adj u y.val)).card := Finset.card_image_le
        _ = _ := h1
        _ ≤ ({n₁, n₂} : Finset V).card := Finset.card_le_card h2
        _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    have hT : (((L u).erase a) \ D).Nonempty := by
      rw [← Finset.card_pos]
      have := Finset.le_card_sdiff D ((L u).erase a)
      rw [Finset.card_erase_of_mem ha, hLu] at this
      omega
    obtain ⟨e, he⟩ := hT
    rw [Finset.mem_sdiff] at he
    obtain ⟨hea, heD⟩ := he
    have hecompat : ∀ y : {y : V // y ≠ u}, G.Adj u y.val → g y ≠ e := by
      intro y hy hcon
      exact heD (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, hcon⟩)
    calc (∏ v : {y : V // y ≠ u}, w v.val (g v))
        = (if (∀ y : {y : V // y ≠ u}, G.Adj u y.val → g y ≠ e) then
            ∏ v : {y : V // y ≠ u}, w v.val (g v) else 0) := by rw [if_pos hecompat]
      _ ≤ ∑ e' ∈ (L u).erase a,
            (if (∀ y : {y : V // y ≠ u}, G.Adj u y.val → g y ≠ e') then
              ∏ v : {y : V // y ≠ u}, w v.val (g v) else 0) :=
          Finset.single_le_sum
            (f := fun e' => if (∀ y : {y : V // y ≠ u}, G.Adj u y.val → g y ≠ e') then
              ∏ v : {y : V // y ≠ u}, w v.val (g v) else 0)
            (fun e' _ => Nat.zero_le _) hea
  · rw [if_neg hcompat]
    exact Nat.zero_le _

end Slack


section PeelInduction

/-- Extracting the root's weight. -/
theorem rootedWcol_root_weight (L : ListAssignment V) (wr : ℕ → ℕ) (r : V) (c : ℕ) :
    rootedWcol G L (fun v e => if v = r then wr e else 1) r c = wr c * rootedCol G L r c := by
  rw [rootedWcol, rootedCol, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [Finset.mem_filter] at hf
  rw [prod_delOption (fun v => if v = r then wr (f v) else 1) r, if_pos rfl, hf.2,
    Finset.prod_congr rfl (fun v _ => if_neg v.property), Finset.prod_const_one, mul_one]

/-- **The peel induction**: peeling every vertex of `T` (away from the root) extracts the
square of its normalizer product, leaving the weight trivial off the root. -/
theorem peel_all {r : V} {k : ℕ} (hk : 4 ≤ k) (L : ListAssignment V)
    (hLcard : ∀ v, (L v).card = k)
    (hnbr : ∀ u, u ≠ r → ∃ n₁ n₂, ∀ y, G.Adj u y → y = n₁ ∨ y = n₂)
    (W : V → ℕ) {c d : ℕ} :
    ∀ (T : Finset V), r ∉ T → ∀ (w : V → ℕ → ℕ),
      (∀ v ∈ T, ∀ c' ∈ L v, ∀ d' ∈ L v, c' ≠ d' → (W v) ^ 2 ≤ w v c' * w v d') →
      (∀ v, v ∉ T → v ≠ r → ∀ e, w v e = 1) →
      (∏ v ∈ T, W v) ^ 2 *
          (rootedWcol G L (fun v e => if v = r then w r e else 1) r c *
            rootedWcol G L (fun v e => if v = r then w r e else 1) r d) ≤
        rootedWcol G L w r c * rootedWcol G L w r d := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ w _ htriv
    have hcong : ∀ c', rootedWcol G L w r c'
        = rootedWcol G L (fun v e => if v = r then w r e else 1) r c' := by
      intro c'
      refine rootedWcol_weight_congr (fun v e _ => ?_) _ _
      by_cases hv : v = r
      · rw [if_pos hv, hv]
      · rw [if_neg hv, htriv v (Finset.notMem_empty v) hv]
    rw [← hcong c, ← hcong d]
    simp
  | @insert u T huT IH =>
    intro hrT w hdomT htriv
    have hur : u ≠ r := fun h => hrT (by rw [← h]; exact Finset.mem_insert_self u T)
    have hrT' : r ∉ T := fun h => hrT (Finset.mem_insert_of_mem h)
    -- peel `u` first
    obtain ⟨n₁, n₂, hn⟩ := hnbr u hur
    have hstep := peel_step (G := G) L w (Ne.symm hur) hk (hLcard u)
      (hdomT u (Finset.mem_insert_self u T)) (c := c) (d := d)
      (fun a ha c' _ => slack_of_two_nbrs (Ne.symm hur) hn hk L (hLcard u) w c' a ha)
    -- then the smaller set, on the `u`-trivialized weight
    have hIH := IH hrT' (fun v e => if v = u then 1 else w v e)
      (fun v hv c' hc' d' hd' hcd' => by
        simp only [if_neg (fun h : v = u => huT (h ▸ hv))]
        exact hdomT v (Finset.mem_insert_of_mem hv) c' hc' d' hd' hcd')
      (fun v hv hvr e => by
        by_cases hvu : v = u
        · rw [if_pos hvu]
        · rw [if_neg hvu]
          exact htriv v (fun h => (Finset.mem_insert.mp h).elim hvu hv) hvr e)
    have hroot : (fun v e => if v = r then
        (fun v' e' => if v' = u then 1 else w v' e') r e else 1)
        = (fun v e => if v = r then w r e else 1) := by
      funext v e
      by_cases hv : v = r
      · rw [if_pos hv, if_pos hv]
        show (if r = u then 1 else w r e) = w r e
        rw [if_neg (fun h : r = u => hur h.symm)]
      · rw [if_neg hv, if_neg hv]
    rw [hroot] at hIH
    calc (∏ v ∈ insert u T, W v) ^ 2 *
          (rootedWcol G L (fun v e => if v = r then w r e else 1) r c *
            rootedWcol G L (fun v e => if v = r then w r e else 1) r d)
        = (W u) ^ 2 * ((∏ v ∈ T, W v) ^ 2 *
            (rootedWcol G L (fun v e => if v = r then w r e else 1) r c *
              rootedWcol G L (fun v e => if v = r then w r e else 1) r d)) := by
          rw [Finset.prod_insert huT]
          ring
      _ ≤ (W u) ^ 2 * (rootedWcol G L (fun v e => if v = u then 1 else w v e) r c *
            rootedWcol G L (fun v e => if v = u then 1 else w v e) r d) :=
          Nat.mul_le_mul_left _ hIH
      _ ≤ rootedWcol G L w r c * rootedWcol G L w r d := hstep


/-- **UM-107 packaged**: on a graph whose non-root vertices have at most two neighbours, the
weighted pair bound reduces to the bare one. -/
theorem pair_bound_of_bare {r : V} {k : ℕ} (hk : 4 ≤ k) (L : ListAssignment V)
    (hLcard : ∀ v, (L v).card = k)
    (hnbr : ∀ u, u ≠ r → ∃ n₁ n₂, ∀ y, G.Adj u y → y = n₁ ∨ y = n₂)
    (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, ∀ c ∈ L v, ∀ d ∈ L v, c ≠ d → (W v) ^ 2 ≤ w v c * w v d)
    (hbare : ∀ c ∈ L r, ∀ d ∈ L r, c ≠ d →
      (rootedCol G (constList V k) r 0) ^ 2 ≤ rootedCol G L r c * rootedCol G L r d) :
    ∀ c ∈ L r, ∀ d ∈ L r, c ≠ d →
      (rootedCol G (constList V k) r 0 * ∏ v, W v) ^ 2 ≤
        rootedWcol G L w r c * rootedWcol G L w r d := by
  intro c hc d hd hcd
  have hpeel := peel_all (G := G) hk L hLcard hnbr W (c := c) (d := d)
    (Finset.univ.erase r) (Finset.notMem_erase r _) w
    (fun v hv => hdom v)
    (fun v hv hvr => absurd (Finset.mem_erase.mpr ⟨hvr, Finset.mem_univ v⟩) hv)
  rw [rootedWcol_root_weight, rootedWcol_root_weight] at hpeel
  have hprod : (∏ v, W v) = W r * ∏ v ∈ Finset.univ.erase r, W v :=
    (Finset.mul_prod_erase Finset.univ W (Finset.mem_univ r)).symm
  calc (rootedCol G (constList V k) r 0 * ∏ v, W v) ^ 2
      = (∏ v ∈ Finset.univ.erase r, W v) ^ 2 *
          ((W r) ^ 2 * (rootedCol G (constList V k) r 0) ^ 2) := by
        rw [hprod]
        ring
    _ ≤ (∏ v ∈ Finset.univ.erase r, W v) ^ 2 *
          ((w r c * w r d) * (rootedCol G L r c * rootedCol G L r d)) := by
        refine Nat.mul_le_mul_left _ (Nat.mul_le_mul ?_ ?_)
        · exact hdom r c hc d hd hcd
        · exact hbare c hc d hd hcd
    _ = (∏ v ∈ Finset.univ.erase r, W v) ^ 2 *
          ((w r c * rootedCol G L r c) * (w r d * rootedCol G L r d)) := by
        ring
    _ ≤ rootedWcol G L w r c * rootedWcol G L w r d := hpeel


end PeelInduction

end ListColoring
