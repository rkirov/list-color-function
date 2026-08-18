/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.BigOperators.Fin
import Cacti.TransferMatrix
import Cacti.RootedProfile

/-!
# The `k = 3` reference tensor and scalar layer

The transfer arithmetic of UM-104 (handoff §5.2, §5.5), below everything that consumes it:
`onesPlus = J + I` on three colours with `(J+I)^s = γ_s · J + I`, the closed form `3γ_s + 1 = 4^s`
and the (5.2) counts; then the scalar step, where `Δ(2q) - Δ(q) < log 2` is cleared of
denominators into a statement of `ℕ`, so no real analysis enters the `k = 3` route at all.
-/

namespace ListColoring

open Finset

section ReferenceTensor

open Matrix

/-- The reference transfer matrix of the `k = 3` tensor argument: `J + I` on three colours
(handoff (5.4)). -/
def onesPlus : Matrix (Fin 3) (Fin 3) ℕ := Matrix.of fun i j => if i = j then 2 else 1

theorem onesPlus_apply (i j : Fin 3) : onesPlus i j = if i = j then 2 else 1 := rfl

/-- Its off-diagonal entry after `s` steps: `γ_{s+1} = 4 γ_s + 1`, that is `γ_s = (4^s - 1)/3`. -/
def gammaPlus : ℕ → ℕ
  | 0 => 0
  | s + 1 => 4 * gammaPlus s + 1

@[simp] theorem gammaPlus_zero : gammaPlus 0 = 0 := rfl
theorem gammaPlus_succ (s : ℕ) : gammaPlus (s + 1) = 4 * gammaPlus s + 1 := rfl

/-- The closed form behind (5.4): `3 γ_s + 1 = 4 ^ s`, i.e. `γ_s = (4 ^ s - 1) / 3`. -/
theorem three_mul_gammaPlus_add_one (s : ℕ) : 3 * gammaPlus s + 1 = 4 ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [gammaPlus_succ, pow_succ]
    omega

/-- **The reference tensor identity** (handoff (5.4)): `(J + I) ^ s = γ_s · J + I` on three
colours. This is the `k = 3` counterpart of `offDiag_pow_apply`, which carries the `k ≥ 4`
transfer arithmetic. -/
theorem onesPlus_pow_apply : ∀ (s : ℕ) (i j : Fin 3),
    (onesPlus ^ s) i j = if i = j then gammaPlus s + 1 else gammaPlus s := by
  intro s
  induction s with
  | zero =>
    intro i j
    by_cases hij : i = j
    · rw [if_pos hij, hij, pow_zero, Matrix.one_apply_eq, gammaPlus_zero]
      rfl
    · rw [if_neg hij, pow_zero, Matrix.one_apply_ne hij, gammaPlus_zero]
  | succ s ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      simp [onesPlus_apply, ih, gammaPlus_succ] <;> omega

/-- **The counts of (5.2)**: with `q = 2 ^ m`, `T = γ_m = (q ^ 2 - 1) / 3`, the uniform cycle
count on `2(m+1)` vertices is `P = 4 ^ (m+1) + 2 = 12 T + 6`. -/
theorem umP_eq_twelve_mul_gammaPlus (m : ℕ) : 4 ^ (m + 1) + 2 = 12 * gammaPlus m + 6 := by
  have h := three_mul_gammaPlus_add_one m
  rw [pow_succ]
  omega

/-- **The marginal of (5.2)**: every one-coordinate marginal `E = 4 T + 2` is exactly `P / 3`. -/
theorem three_mul_umE (m : ℕ) : 3 * (4 * gammaPlus m + 2) = 4 ^ (m + 1) + 2 := by
  have h := three_mul_gammaPlus_add_one m
  rw [pow_succ]
  omega

end ReferenceTensor

section ScalarStep

/-! The scalar layer of UM-104 (handoff §5.5). Writing `D(q) = (q+1)^(q+1) / q^q = e^{Δ(q)}`,
the induction step `Δ(2q) - Δ(q) < log 2` is `D(2q) < 2 D(q)`, and clearing denominators turns it
into a statement of `ℕ` — so no `Real.log` is needed anywhere. -/

/-- Bernoulli in `ℕ`, no subtraction. -/
theorem bernoulli_nat (B : ℕ) :
    ∀ q : ℕ, (B + 1) ^ (q + 1) ≤ B ^ (q + 1) + (q + 1) * (B + 1) ^ q := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have hBA : B ^ (q + 1) ≤ (B + 1) ^ (q + 1) := Nat.pow_le_pow_left (Nat.le_succ B) _
    calc (B + 1) ^ (q + 2) = (B + 1) * (B + 1) ^ (q + 1) := by ring
      _ ≤ (B + 1) * (B ^ (q + 1) + (q + 1) * (B + 1) ^ q) := Nat.mul_le_mul_left _ ih
      _ = B ^ (q + 2) + B ^ (q + 1) + (q + 1) * (B + 1) ^ (q + 1) := by ring
      _ ≤ B ^ (q + 2) + (B + 1) ^ (q + 1) + (q + 1) * (B + 1) ^ (q + 1) := by gcongr
      _ = B ^ (q + 2) + (q + 2) * (B + 1) ^ (q + 1) := by ring

/-- Abstract core: `A = B + 1`, and `n * c < A` gives `A ^ n * (c - 1) < B ^ n * c`. -/
theorem core_step (B n c : ℕ) (hn : 1 ≤ n) (hc : n * c < B + 1) :
    (B + 1) ^ n * c < B ^ n * c + (B + 1) ^ n := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have hb := bernoulli_nat B p
  have hsmall : (p + 1) * c * (B + 1) ^ p < (B + 1) ^ (p + 1) := by
    calc (p + 1) * c * (B + 1) ^ p < (B + 1) * (B + 1) ^ p :=
          (Nat.mul_lt_mul_right (Nat.pow_pos (show 0 < B + 1 by omega))).mpr hc
      _ = (B + 1) ^ (p + 1) := by ring
  calc (B + 1) ^ (p + 1) * c ≤ (B ^ (p + 1) + (p + 1) * (B + 1) ^ p) * c :=
        Nat.mul_le_mul_right _ hb
    _ = B ^ (p + 1) * c + (p + 1) * c * (B + 1) ^ p := by ring
    _ < B ^ (p + 1) * c + (B + 1) ^ (p + 1) := by omega

/-- **The scalar induction step of handoff (5.15), exponentiated**: `Δ(2q) - Δ(q) < log 2` is
exactly
`D(2q) < 2 D(q)` for `D(q) = (q+1)^(q+1)/q^q`, i.e. this pure `ℕ` inequality. -/
theorem delta_step (q : ℕ) (hq : 1 ≤ q) :
    (2 * q + 1) ^ (2 * q + 1) < (2 * q) ^ q * (2 * q + 2) ^ (q + 1) := by
  have hA : (2 * q + 1) ^ 2 = 2 * q * (2 * q + 2) + 1 := by ring
  have hL : (2 * q + 1) ^ (2 * q + 1)
      = (2 * q * (2 * q + 2) + 1) ^ q * (2 * q + 1) := by
    rw [← hA, ← pow_mul, ← pow_succ]
  have hR : (2 * q) ^ q * (2 * q + 2) ^ (q + 1)
      = (2 * q * (2 * q + 2)) ^ q * (2 * q + 2) := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
  rw [hL, hR]
  have hc : q * (2 * q + 2) < 2 * q * (2 * q + 2) + 1 := by nlinarith
  have h := core_step (2 * q * (2 * q + 2)) q (2 * q + 2) hq hc
  have hsplit : (2 * q * (2 * q + 2) + 1) ^ q * (2 * q + 2)
      = (2 * q * (2 * q + 2) + 1) ^ q * (2 * q + 1) + (2 * q * (2 * q + 2) + 1) ^ q := by ring
  omega

end ScalarStep

/-- **The `k = 3` bridge inequality**: `(a+b)(b+c)(c+a) ≥ 8abc`, the AM–GM behind the pendant
factor `2` at list size three. -/
theorem gm_bridge (a b c : ℕ) : 8 * (a * b * c) ≤ (b + c) * (a + c) * (a + b) := by
  zify
  nlinarith [mul_nonneg (sq_nonneg ((a : ℤ) - b)) (Int.natCast_nonneg c),
    mul_nonneg (sq_nonneg ((b : ℤ) - c)) (Int.natCast_nonneg a),
    mul_nonneg (sq_nonneg ((a : ℤ) - c)) (Int.natCast_nonneg b)]

/-- The bridge inequality as the pendant step consumes it: on a three-element list, the product
of the complementary sums clears `8` times the product of the weights. -/
theorem gm_bridge_prod {s : Finset ℕ} (hs : s.card = 3) (w : ℕ → ℕ) :
    8 * ∏ e ∈ s, w e ≤ ∏ e ∈ s, ∑ d ∈ s.erase e, w d := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hs
  have hx : ({x, y, z} : Finset ℕ).erase x = {y, z} := by
    ext e
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hne, rfl | rfl | rfl⟩
      · exact absurd rfl hne
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨fun h => hxy h.symm, Or.inr (Or.inl rfl)⟩
      · exact ⟨fun h => hxz h.symm, Or.inr (Or.inr rfl)⟩
  have hy : ({x, y, z} : Finset ℕ).erase y = {x, z} := by
    ext e
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hne, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact absurd rfl hne
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hxy, Or.inl rfl⟩
      · exact ⟨fun h => hyz h.symm, Or.inr (Or.inr rfl)⟩
  have hz : ({x, y, z} : Finset ℕ).erase z = {x, y} := by
    ext e
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hne, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hne
    · rintro (rfl | rfl)
      · exact ⟨hxz, Or.inl rfl⟩
      · exact ⟨hyz, Or.inr (Or.inl rfl)⟩
  rw [Finset.prod_insert (by simp [hxy, hxz]), Finset.prod_insert (by simp [hyz]),
    Finset.prod_singleton, Finset.prod_insert (by simp [hxy, hxz]),
    Finset.prod_insert (by simp [hyz]), Finset.prod_singleton, hx, hy, hz,
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton,
    Finset.sum_insert (by simp [hxz]), Finset.sum_singleton,
    Finset.sum_insert (by simp [hxy]), Finset.sum_singleton]
  calc 8 * (w x * (w y * w z)) = 8 * (w x * w y * w z) := by ring
    _ ≤ (w y + w z) * (w x + w z) * (w x + w y) := gm_bridge _ _ _
    _ = (w y + w z) * ((w x + w z) * (w x + w y)) := by ring


/-- The `ℕ` form of AM–GM in product form, for weight families. -/
theorem card_pow_mul_prod_le_sum_pow_nat {α : Type*} (T : Finset α) (x : α → ℕ) :
    T.card ^ T.card * ∏ a ∈ T, x a ≤ (∑ a ∈ T, x a) ^ T.card := by
  have h := card_pow_mul_prod_le_sum_pow' T (fun a => (x a : ℝ)) (fun a _ => Nat.cast_nonneg _)
  exact_mod_cast h


/-- **Weighted AM–GM with integral masses** (handoff (5.18)): for masses `U` summing to `P`,
`P ^ P * ∏ X ^ U ≤ (∑ X) ^ P * ∏ U ^ U`. Cleared of denominators, so it stays in `ℕ`. -/
theorem weighted_amgm_masses {α : Type*} (T : Finset α) (X U : α → ℕ) {P : ℕ} (hP : 0 < P)
    (hsum : ∑ a ∈ T, U a = P) (hU : ∀ a ∈ T, 0 < U a) :
    P ^ P * ∏ a ∈ T, X a ^ U a ≤ (∑ a ∈ T, X a) ^ P * ∏ a ∈ T, U a ^ U a := by
  classical
  have hPR : (0:ℝ) < (P:ℝ) := by exact_mod_cast hP
  have hwsum : ∑ a ∈ T, ((U a : ℝ)) = (P:ℝ) := by
    rw [← Nat.cast_sum, hsum]
  have hz : ∀ a ∈ T, (0:ℝ) ≤ (X a : ℝ) / (U a : ℝ) := fun a _ => by positivity
  have h := Real.geom_mean_le_arith_mean T (fun a => (U a : ℝ)) (fun a => (X a : ℝ) / (U a : ℝ))
    (fun a _ => by positivity) (by rw [hwsum]; exact hPR) hz
  rw [hwsum] at h
  have harith : ∑ a ∈ T, ((U a : ℝ) * ((X a : ℝ) / (U a : ℝ))) = ∑ a ∈ T, (X a : ℝ) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have : ((U a : ℝ)) ≠ 0 := by
      have := hU a ha
      positivity
    field_simp
  rw [harith] at h
  -- raise to the `P`-th power
  have hprodnn : (0:ℝ) ≤ ∏ a ∈ T, ((X a : ℝ) / (U a : ℝ)) ^ ((U a : ℕ) : ℝ) :=
    Finset.prod_nonneg fun a ha => Real.rpow_nonneg (hz a ha) _
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hprodnn _) h (le_of_lt hPR)
  rw [← Real.rpow_mul hprodnn, inv_mul_cancel₀ (ne_of_gt hPR), Real.rpow_one] at hpow
  -- convert rpow to npow and clear denominators
  have hL : ∏ a ∈ T, ((X a : ℝ) / (U a : ℝ)) ^ ((U a : ℕ) : ℝ)
      = ∏ a ∈ T, ((X a : ℝ) / (U a : ℝ)) ^ (U a) := by
    exact Finset.prod_congr rfl fun a _ => Real.rpow_natCast _ _
  rw [hL] at hpow
  have hR : (((∑ a ∈ T, (X a : ℝ)) / (P:ℝ)) ^ ((P:ℕ) : ℝ))
      = ((∑ a ∈ T, (X a : ℝ)) / (P:ℝ)) ^ P := Real.rpow_natCast _ _
  rw [hR] at hpow
  -- multiply through
  have hUpos : ∀ a ∈ T, (0:ℝ) < (U a : ℝ) := fun a ha => by
    have := hU a ha; positivity
  have hprodU : (0:ℝ) < ∏ a ∈ T, ((U a : ℝ)) ^ (U a) :=
    Finset.prod_pos fun a ha => pow_pos (hUpos a ha) _
  have hsplit : ∏ a ∈ T, ((X a : ℝ)) ^ (U a)
      = (∏ a ∈ T, ((X a : ℝ) / (U a : ℝ)) ^ (U a)) * ∏ a ∈ T, ((U a : ℝ)) ^ (U a) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [← mul_pow, div_mul_cancel₀ _ (ne_of_gt (hUpos a ha))]
  have h2 : ((P:ℝ)) ^ P * (∏ a ∈ T, ((X a : ℝ) / (U a : ℝ)) ^ (U a))
      ≤ (∑ a ∈ T, (X a : ℝ)) ^ P := by
    have hPp : (0:ℝ) < ((P:ℝ)) ^ P := by positivity
    calc ((P:ℝ)) ^ P * (∏ a ∈ T, ((X a : ℝ) / (U a : ℝ)) ^ (U a))
        ≤ ((P:ℝ)) ^ P * (((∑ a ∈ T, (X a : ℝ)) / (P:ℝ)) ^ P) :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt hPp)
      _ = (∑ a ∈ T, (X a : ℝ)) ^ P := by
          rw [div_pow]
          field_simp
  have key : ((P:ℝ)) ^ P * ∏ a ∈ T, ((X a : ℝ)) ^ (U a)
      ≤ (∑ a ∈ T, (X a : ℝ)) ^ P * ∏ a ∈ T, ((U a : ℝ)) ^ (U a) := by
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h2 (le_of_lt hprodU)
  exact_mod_cast key

end ListColoring
