/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Defs

/-!
# The bridge inequality

The transport step across a bridge or pendant edge (handoff §4.2): if a weight vector on a
`k`-element list is pair-dominant over `W` — every two distinct colours have weight product at
least `W²` — then every complementary sum is at least `(k-1)·W`.

Entirely in `ℕ`: the two-valued analysis reduces to the factored inequality
`(W - wₐ)·((k-2)·W - wₐ) ≥ 0` at the minimum coordinate `wₐ ≤ W`, cleared of division by
multiplying through by `wₐ`.
-/

namespace ListColoring

open Finset

/-- **The bridge inequality.** On a list `s` of size `k ≥ 3`, a pair-dominant weight has every
complementary sum at least `(k-1)·W`. -/
theorem bridge_sum_ge {s : Finset ℕ} {k : ℕ} (hk : 3 ≤ k) (hcard : s.card = k)
    {w : ℕ → ℕ} {W : ℕ} (hdom : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → W ^ 2 ≤ w c * w d)
    {c : ℕ} (hc : c ∈ s) :
    (k - 1) * W ≤ ∑ e ∈ s.erase c, w e := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  have hce : (s.erase c).card = m + 2 := by
    rw [Finset.card_erase_of_mem hc, hcard]
    omega
  have hgoal : (m + 3 - 1) * W = (m + 2) * W := by norm_num
  rw [hgoal]
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image w ⟨c, hc⟩
  by_cases hW : W = 0
  · simp [hW]
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW
  by_cases haW : W ≤ w a
  · -- all coordinates at least `W`
    have hterm : ∀ e ∈ s.erase c, W ≤ w e := fun e he =>
      le_trans haW (hmin e (Finset.mem_of_mem_erase he))
    calc (m + 2) * W = (s.erase c).card • W := by rw [hce, smul_eq_mul]
      _ ≤ ∑ e ∈ s.erase c, w e := Finset.card_nsmul_le_sum _ _ _ hterm
  · push Not at haW
    have hapos : 0 < w a := by
      rcases Nat.eq_zero_or_pos (w a) with h0 | h0
      · exfalso
        obtain ⟨d, hd, hda⟩ : ∃ d ∈ s, d ≠ a := by
          have h2 : 1 < s.card := by omega
          obtain ⟨d, hd, e, he, hde⟩ := Finset.one_lt_card.mp h2
          by_cases hda : d = a
          · exact ⟨e, he, fun h => hde (h ▸ hda ▸ rfl)⟩
          · exact ⟨d, hd, hda⟩
        have hpair := hdom d hd a ha hda
        rw [h0, Nat.mul_zero, Nat.le_zero, pow_eq_zero_iff (two_ne_zero)] at hpair
        exact hW hpair
      · exact h0
    have hother : ∀ e ∈ s, e ≠ a → W ^ 2 ≤ w a * w e := fun e he hea =>
      hdom a ha e he (fun h => hea h.symm)
    by_cases hca : c = a
    · -- the deficient coordinate is excluded: every remaining term clears `W`
      subst hca
      have hterm : ∀ e ∈ s.erase c, W ≤ w e := by
        intro e he
        have h2 := hother e (Finset.mem_of_mem_erase he) (Finset.ne_of_mem_erase he)
        by_contra hlt
        push Not at hlt
        have : w c * w e < W * W := by
          calc w c * w e ≤ w e * w e :=
                Nat.mul_le_mul_right _ (hmin e (Finset.mem_of_mem_erase he))
            _ < W * W := Nat.mul_lt_mul_of_lt_of_le hlt (le_of_lt hlt) hWpos
        rw [pow_two] at h2
        omega
      calc (m + 2) * W = (s.erase c).card • W := by rw [hce, smul_eq_mul]
        _ ≤ ∑ e ∈ s.erase c, w e := Finset.card_nsmul_le_sum _ _ _ hterm
    · -- the deficient coordinate survives: multiply through by `wₐ` and factor
      have haerase : a ∈ s.erase c := Finset.mem_erase.mpr ⟨fun h => hca h.symm, ha⟩
      have hsplit : ∑ e ∈ s.erase c, w e = w a + ∑ e ∈ (s.erase c).erase a, w e :=
        (Finset.add_sum_erase _ w haerase).symm
      have hcard2 : ((s.erase c).erase a).card = m + 1 := by
        rw [Finset.card_erase_of_mem haerase, hce]
        omega
      have hbound : (m + 1) * W ^ 2 ≤ w a * ∑ e ∈ (s.erase c).erase a, w e := by
        rw [Finset.mul_sum]
        calc (m + 1) * W ^ 2 = ((s.erase c).erase a).card • W ^ 2 := by
              rw [hcard2, smul_eq_mul]
          _ ≤ ∑ e ∈ (s.erase c).erase a, w a * w e := by
              refine Finset.card_nsmul_le_sum _ _ _ fun e he => ?_
              exact hother e (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he))
                (Finset.ne_of_mem_erase he)
      have hfact : w a * ((m + 2) * W) ≤ w a * w a + (m + 1) * W ^ 2 := by
        have h3 : (w a : ℤ) ≤ (W : ℤ) := by exact_mod_cast le_of_lt haW
        have h4 : (w a : ℤ) ≤ (m + 1 : ℤ) * W := by nlinarith
        zify
        nlinarith [mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h4)]
      have hmul : w a * ((m + 2) * W) ≤ w a * ∑ e ∈ s.erase c, w e := by
        rw [hsplit, Nat.mul_add]
        calc w a * ((m + 2) * W) ≤ w a * w a + (m + 1) * W ^ 2 := hfact
          _ ≤ w a * w a + w a * ∑ e ∈ (s.erase c).erase a, w e :=
              Nat.add_le_add_left hbound _
      exact Nat.le_of_mul_le_mul_left hmul hapos

end ListColoring
