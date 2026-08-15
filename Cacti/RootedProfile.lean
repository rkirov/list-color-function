/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.MeanInequalities
import Cacti.Defs

/-!
# Rooted-profile message algebra

The cactus induction (handoff §4, §6.5) passes **rooted profiles** — vectors of rooted coloring
counts indexed by root colors — up a block-cut tree. This file is the profile algebra layer: it
knows nothing about graphs. Everything here is `sorry`-free.

The invariant carried at `k ≥ 4` is the **pair bound** `P'`: every pair of distinct coordinates
has product at least `A²`, where `A` is the block's uniform normalizer. Following the review's
simplification, subset products are never needed with roots: the terminal closure needs only
`A ^ k ≤ ∏ x`, which follows from the pair bounds alone by the **cyclic pairing**
`(∏ x)² = ∏ c, x c * x (c + 1) ≥ (A²)^k`. A single k-th root survives, in the terminal AM–GM
(`PairBound.card_mul_le_sum`), which is Mathlib's weighted AM–GM.

* `PairBound A x`   — `∀ c ≠ d, A² ≤ x c * x d`
* `PairBound.mul`   — cut-vertex composition: profiles multiply, normalizers multiply
* `PairBound.pow_card_le_prod` — `A ^ k ≤ ∏ x` (cyclic pairing; no roots)
* `PairBound.card_mul_le_sum`  — `k * A ≤ ∑ x` (terminal AM–GM closure)
-/

namespace ListColoring

open Finset

/-- The pair invariant `P'` on a profile `x : Fin k → ℝ` with normalizer `A`: any two distinct
coordinates have product at least `A ^ 2`. -/
def PairBound {k : ℕ} (A : ℝ) (x : Fin k → ℝ) : Prop :=
  ∀ ⦃c d : Fin k⦄, c ≠ d → A ^ 2 ≤ x c * x d

namespace PairBound

variable {k : ℕ} {A B : ℝ} {x y : Fin k → ℝ}

/-- Cut-vertex composition: pointwise products of `P'` profiles satisfy `P'` with the product
normalizer. No nonnegativity hypotheses: the pair bounds themselves supply what is needed. -/
theorem mul (hxp : PairBound A x) (hyp : PairBound B y) :
    PairBound (A * B) (fun c => x c * y c) := by
  intro c d hcd
  have hx2 : A ^ 2 ≤ x c * x d := hxp hcd
  have hy2 : B ^ 2 ≤ y c * y d := hyp hcd
  calc (A * B) ^ 2 = A ^ 2 * B ^ 2 := by ring
    _ ≤ (x c * x d) * (y c * y d) :=
        mul_le_mul hx2 hy2 (sq_nonneg B) (le_trans (sq_nonneg A) hx2)
    _ = (x c * y c) * (x d * y d) := by ring

/-- The cyclic pairing bound: pair bounds alone give `A ^ k ≤ ∏ x`, with no `|S|`-th roots.
Squares both sides and pairs coordinate `c` with `c + 1` around `Fin k`. -/
theorem pow_card_le_prod (hk : 2 ≤ k) (hA : 0 ≤ A) (hx : ∀ c, 0 ≤ x c)
    (h : PairBound A x) : A ^ k ≤ ∏ c, x c := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hone : (1 : Fin (m + 2)) ≠ 0 := by
    intro h1
    exact absurd (congrArg Fin.val h1) (by simp)
  have hstep : ∀ c : Fin (m + 2), c ≠ c + 1 := by
    intro c hc
    have h0 : c + 0 = c + 1 := by rw [add_zero]; exact hc
    exact hone (add_left_cancel h0).symm
  have hshift : ∏ c : Fin (m + 2), x (c + 1) = ∏ c, x c :=
    Fintype.prod_equiv (Equiv.addRight (1 : Fin (m + 2))) _ _ fun _ => rfl
  have hprod2 : ∏ c : Fin (m + 2), (x c * x (c + 1)) = (∏ c, x c) ^ 2 := by
    rw [prod_mul_distrib, hshift, sq]
  have hsq : ((A ^ (m + 2)) : ℝ) ^ 2 ≤ (∏ c, x c) ^ 2 := by
    calc (A ^ (m + 2)) ^ 2 = ∏ _c : Fin (m + 2), (A ^ 2) := by
          rw [prod_const, card_univ, Fintype.card_fin]; ring
      _ ≤ ∏ c : Fin (m + 2), (x c * x (c + 1)) :=
          prod_le_prod (fun _ _ => sq_nonneg A) (fun c _ => h (hstep c))
      _ = (∏ c, x c) ^ 2 := hprod2
  have hxprod : 0 ≤ ∏ c, x c := prod_nonneg fun c _ => hx c
  have hApow : 0 ≤ A ^ (m + 2) := pow_nonneg hA _
  nlinarith [hsq, hxprod, hApow]

/-- The terminal AM–GM closure: pair bounds give `k * A ≤ ∑ x`. This is the final inequality of
the cactus induction (handoff (6.16)): at the root, `∑ x = P(G, L)` and `k * A = P(G, k)`. -/
theorem card_mul_le_sum (hk : 2 ≤ k) (hA : 0 ≤ A) (hx : ∀ c, 0 ≤ x c)
    (h : PairBound A x) : (k : ℝ) * A ≤ ∑ c, x c := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hprod : A ^ k ≤ ∏ c, x c := pow_card_le_prod hk hA hx h
  set r : ℝ := 1 / (k : ℝ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hgm : ∏ c, x c ^ r ≤ ∑ c, r * x c :=
    Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => r) x
      (fun _ _ => hr0)
      (by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hr]
        field_simp)
      (fun c _ => hx c)
  have hgeom : (∏ c, x c) ^ r = ∏ c, x c ^ r :=
    (Real.finsetProd_rpow Finset.univ x (fun c _ => hx c) r).symm
  have hAk : ((A ^ k : ℝ)) ^ r = A := by
    rw [← Real.rpow_natCast A k, ← Real.rpow_mul hA, hr, mul_one_div,
      div_self (ne_of_gt hk0), Real.rpow_one]
  have hA' : A ≤ (∏ c, x c) ^ r := by
    have h1 : ((A ^ k : ℝ)) ^ r ≤ (∏ c, x c) ^ r :=
      Real.rpow_le_rpow (pow_nonneg hA k) hprod hr0
    exact hAk ▸ h1
  have hchain : A ≤ r * ∑ c, x c := by
    calc A ≤ (∏ c, x c) ^ r := hA'
      _ = ∏ c, x c ^ r := hgeom
      _ ≤ ∑ c, r * x c := hgm
      _ = r * ∑ c, x c := by rw [mul_sum]
  calc (k : ℝ) * A ≤ (k : ℝ) * (r * ∑ c, x c) :=
        mul_le_mul_of_nonneg_left hchain (le_of_lt hk0)
    _ = ∑ c, x c := by rw [hr]; field_simp

end PairBound

end ListColoring
