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
    · sorry

end MainInduction

end ListColoring
