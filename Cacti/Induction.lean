/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
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

end ListColoring
