/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Induction

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


end ListColoring
