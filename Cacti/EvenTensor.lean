/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Cacti.Tensor
import Cacti.Induction

/-! Pinning of the arithmetic + residual layer of UM-104, handoff §5.2–§5.3. -/

open Matrix Finset

namespace ListColoring

/-! ### (a) The γ addition law -/

/-- **(a)** `γ_{a+b} = 3 γ_a γ_b + γ_a + γ_b`: the multiplicativity of `3γ_s + 1 = 4^s`,
i.e. the law that lets a cycle transfer product be split into two arcs. -/
theorem gammaPlus_add (a b : ℕ) :
    gammaPlus (a + b) = 3 * gammaPlus a * gammaPlus b + gammaPlus a + gammaPlus b := by
  have ha := three_mul_gammaPlus_add_one a
  have hb := three_mul_gammaPlus_add_one b
  have hab := three_mul_gammaPlus_add_one (a + b)
  rw [pow_add, ← ha, ← hb] at hab
  have h : 3 * gammaPlus (a + b) + 1
      = 3 * (3 * gammaPlus a * gammaPlus b + gammaPlus a + gammaPlus b) + 1 := by
    rw [hab]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (Nat.add_right_cancel h)

/-! ### (b) The cut / closed transfer identities -/

/-- `J + P_σ` on three colours: weight `2` on the σ-graph, `1` off it.  For `σ = 1` this is
`onesPlus = J + I`. -/
def onesPerm (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℕ :=
  Matrix.of fun i j => if j = σ i then 2 else 1

theorem onesPerm_apply (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    onesPerm σ i j = if j = σ i then 2 else 1 := rfl

theorem onesPerm_one : onesPerm 1 = onesPlus := by
  ext i j; simp [onesPerm_apply, onesPlus_apply, eq_comm]

/-- **(b), master form**: `(J + I) ^ s * (J + P_σ) = γ_{s+1} · J + P_σ`. -/
theorem onesPlus_pow_mul_onesPerm (s : ℕ) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (onesPlus ^ s * onesPerm σ) i j
      = gammaPlus (s + 1) + (if j = σ i then 1 else 0) := by
  have hcond : ∀ k : Fin 3, (j = σ k) ↔ (σ.symm j = k) := by
    intro k
    constructor
    · rintro rfl; exact σ.symm_apply_apply k
    · rintro rfl; exact (σ.apply_symm_apply j).symm
  rw [Matrix.mul_apply]
  simp only [onesPlus_pow_apply, onesPerm_apply, hcond]
  clear hcond
  rw [Fin.sum_univ_three, gammaPlus_succ]
  generalize σ.symm j = u
  fin_cases i <;> fin_cases u <;> simp <;> ring

/-- **(b), closed form** — the full cycle transfer product on `M` terminal positions:
`(J + I) ^ (M - 1) * (J + P_σ) = γ_M · J + P_σ`.  Its trace `3 γ_M + fix σ = 4 ^ M + fix σ - 1`
is `Σ_a 2 ^ h(a)` of handoff (5.4)/(2.3) at `z = 2`, and its diagonal `γ_M + [σ i = i]` gives,
after the constant-word correction of (5.3), the one-coordinate marginal `γ_M + 1 = E`. -/
theorem onesPlus_pow_mul_onesPerm_closed (M : ℕ) (hM : 1 ≤ M) (σ : Equiv.Perm (Fin 3))
    (i j : Fin 3) :
    (onesPlus ^ (M - 1) * onesPerm σ) i j = gammaPlus M + (if j = σ i then 1 else 0) := by
  obtain ⟨M, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  simpa using onesPlus_pow_mul_onesPerm M σ i j

/-- **(b), cut form** — the product of the `M - 1` transfer matrices that remain after one
ordinary edge is cut out of the cycle: `(J + I) ^ (M - 2) * (J + P_σ) = γ_{M-1} · J + P_σ`.
With `T = γ_{M-1}` this is the `T · J + P_σ` entering every ordinary pair marginal. -/
theorem onesPlus_pow_mul_onesPerm_cut (M : ℕ) (hM : 2 ≤ M) (σ : Equiv.Perm (Fin 3))
    (i j : Fin 3) :
    (onesPlus ^ (M - 2) * onesPerm σ) i j
      = gammaPlus (M - 1) + (if j = σ i then 1 else 0) := by
  obtain ⟨M, rfl⟩ : ∃ N, M = N + 2 := ⟨M - 2, by omega⟩
  simpa using onesPlus_pow_mul_onesPerm M σ i j

/-- The marginal identity of (5.2): `γ_M + 1 = 4 T + 2 = E` with `T = γ_{M-1}`. -/
theorem umE_eq_gammaPlus_succ (m : ℕ) : gammaPlus (m + 1) + 1 = 4 * gammaPlus m + 2 := by
  rw [gammaPlus_succ]

/-! ### (c) The residual table of §5.3 -/

/-- Residual of an ordinary terminal pair against base `(M, S) = (2T, T)`:
`D = I + P_{σ⁻¹}`, i.e. `D i j = [i = j] + [i = σ j]`. -/
def resOrd (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℕ :=
  Matrix.of fun i j => (if i = j then 1 else 0) + (if i = σ j then 1 else 0)

/-- Residual of the closing terminal pair, in aligned coordinates, against the naive base
`(2T, T)`: `D = 2 P_{σ⁻¹}`. -/
def resClose (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℕ :=
  Matrix.of fun i j => 2 * (if i = σ j then 1 else 0)

/-- Residual of the closing terminal pair against the **repaired** base `(2T - 2, T)`:
`D = 2 P_{σ⁻¹} + 2 I`. -/
def resCloseRepaired (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) ℕ :=
  Matrix.of fun i j => 2 * (if i = σ j then 1 else 0) + 2 * (if i = j then 1 else 0)

/-- The three-cycle `0 ↦ 1 ↦ 2 ↦ 0`. -/
def threeCycle : Equiv.Perm (Fin 3) := Equiv.addRight (1 : Fin 3)

/-- **(c) base/residual split, ordinary edge.**  The exact pair marginal of `U` at an ordinary
terminal pair is `(J + I)(i,j) * (T·J + P_σ)(j,i)` plus the constant-word correction of (5.3);
it splits as base `M = 2T` on the selected matching, `S = T` off it, plus residual `resOrd σ`. -/
theorem pairOrdinary_decomp (T : ℕ) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (if i = j then 2 else 1) * (T + (if i = σ j then 1 else 0))
        + (if i = j ∧ σ i ≠ i then 1 else 0)
      = (if i = j then 2 * T else T) + resOrd σ i j := by
  simp only [resOrd, Matrix.of_apply]
  rcases eq_or_ne i j with rfl | h
  · rcases eq_or_ne (σ i) i with hf | hf
    · simp [hf]; omega
    · simp [hf, Ne.symm hf]
  · simp [h]

/-- **(c) base/residual split, closing edge, naive base `(2T, T)`.**  In aligned coordinates the
closing pair marginal is `(if i = j then 2 else 1) * (T + [i = σ j])` plus the correction, now
sitting at `i = σ j`; the residual is `resClose σ = 2 P_{σ⁻¹}`. -/
theorem pairClosing_decomp (T : ℕ) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (if i = j then 2 else 1) * (T + (if i = σ j then 1 else 0))
        + (if i = σ j ∧ σ i ≠ i then 1 else 0)
      = (if i = j then 2 * T else T) + resClose σ i j := by
  simp only [resClose, Matrix.of_apply]
  rcases eq_or_ne i j with rfl | h
  · rcases eq_or_ne (σ i) i with hf | hf
    · simp [hf]; omega
    · simp [hf, Ne.symm hf]
  · rcases eq_or_ne i (σ j) with hs | hs
    · have hjj : σ j ≠ j := fun hh => h (hs.trans hh)
      simp [hs, hjj]
    · simp [h, hs]

/-- **(c) base/residual split, closing edge, repaired base `(2T - 2, T)`** (written with
`T = S + 1` to stay in `ℕ`): the residual becomes `resCloseRepaired σ = 2 P_{σ⁻¹} + 2 I`,
with row/column demand `d = 4`. -/
theorem pairClosing_decomp_repaired (S : ℕ) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (if i = j then 2 else 1) * ((S + 1) + (if i = σ j then 1 else 0))
        + (if i = σ j ∧ σ i ≠ i then 1 else 0)
      = (if i = j then 2 * S else S + 1) + resCloseRepaired σ i j := by
  simp only [resCloseRepaired, Matrix.of_apply]
  rcases eq_or_ne i j with rfl | h
  · rcases eq_or_ne (σ i) i with hf | hf
    · simp [hf]; omega
    · simp [hf, Ne.symm hf]; omega
  · rcases eq_or_ne i (σ j) with hs | hs
    · have hjj : σ j ≠ j := fun hh => h (hs.trans hh)
      simp [hs, hjj]
    · simp [h, hs]

/-! #### The concrete integer matrices of the table -/

/-- Identity holonomy (the UM-099 case): both residuals are `2 I`. -/
theorem resOrd_one : resOrd 1 = !![2, 0, 0; 0, 2, 0; 0, 0, 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [resOrd]

theorem resClose_one : resClose 1 = !![2, 0, 0; 0, 2, 0; 0, 0, 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [resClose]

/-- Transposition holonomy, ordinary edge: `D = [[1,1,0],[1,1,0],[0,0,2]]`, `d = 2`. -/
theorem resOrd_swap : resOrd (Equiv.swap 0 1) = !![1, 1, 0; 1, 1, 0; 0, 0, 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [resOrd, Equiv.swap_apply_def]

/-- Transposition holonomy, closing edge, **naive** base `(2T, T)`:
`D = 2 P_σ = [[0,2,0],[2,0,0],[0,0,2]]`. -/
theorem resClose_swap : resClose (Equiv.swap 0 1) = !![0, 2, 0; 2, 0, 0; 0, 0, 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [resClose, Equiv.swap_apply_def]

/-- Transposition holonomy, closing edge, **repaired** base `(2T - 2, T)`:
`D = [[2,2,0],[2,2,0],[0,0,4]]`, `d = 4`. -/
theorem resCloseRepaired_swap :
    resCloseRepaired (Equiv.swap 0 1) = !![2, 2, 0; 2, 2, 0; 0, 0, 4] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [resCloseRepaired, Equiv.swap_apply_def]

/-- Three-cycle holonomy, ordinary edge: `D = [[1,0,1],[1,1,0],[0,1,1]]`, `d = 2`. -/
theorem resOrd_threeCycle : resOrd threeCycle = !![1, 0, 1; 1, 1, 0; 0, 1, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [resOrd, threeCycle]

/-- Three-cycle holonomy, closing edge: `D = 2 P_{σ⁻¹} = [[0,0,2],[2,0,0],[0,2,0]]`, `d = 2`;
no repair is needed. -/
theorem resClose_threeCycle : resClose threeCycle = !![0, 0, 2; 2, 0, 0; 0, 2, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [resClose, threeCycle]

/-! #### The routing hypotheses (5.8) = (3.2) -/

/-- Every ordinary residual has all row sums `d = 2`. -/
theorem resOrd_rowSum (σ : Equiv.Perm (Fin 3)) (i : Fin 3) : ∑ j, resOrd σ i j = 2 := by
  have hc : ∀ j : Fin 3, (i = σ j) ↔ (σ.symm i = j) := by
    intro j
    constructor
    · rintro rfl; exact σ.symm_apply_apply j
    · rintro rfl; exact (σ.apply_symm_apply i).symm
  simp only [resOrd, Matrix.of_apply, Finset.sum_add_distrib, hc]
  simp

/-- Every ordinary residual has all column sums `d = 2`. -/
theorem resOrd_colSum (σ : Equiv.Perm (Fin 3)) (j : Fin 3) : ∑ i, resOrd σ i j = 2 := by
  simp [resOrd, Finset.sum_add_distrib]

/-- The capacitated-Hall hypothesis (5.8) holds for every ordinary residual, `d = 2`. -/
theorem resOrd_hall (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) (h : i ≠ j) :
    resOrd σ i j + resOrd σ j i ≤ 2 := by
  simp only [resOrd, Matrix.of_apply, if_neg h, if_neg (Ne.symm h)]
  split <;> split <;> simp

/-- The three-cycle closing residual satisfies (5.8) with `d = 2`. -/
theorem resClose_threeCycle_hall (i j : Fin 3) (h : i ≠ j) :
    resClose threeCycle i j + resClose threeCycle j i ≤ 2 := by
  rw [resClose_threeCycle]
  fin_cases i <;> fin_cases j <;> simp_all

/-- The repaired transposition closing residual satisfies (5.8) with `d = 4`. -/
theorem resCloseRepaired_swap_hall (i j : Fin 3) (h : i ≠ j) :
    resCloseRepaired (Equiv.swap 0 1) i j + resCloseRepaired (Equiv.swap 0 1) j i ≤ 4 := by
  rw [resCloseRepaired_swap]
  fin_cases i <;> fin_cases j <;> simp_all

/-- **The repair is necessary.**  With the naive base `(2T, T)` the transposition closing
residual `2 P_σ` violates (5.8) at the moved pair: `D 0 1 + D 1 0 = 4 > 2 = d`. -/
theorem resClose_swap_hall_fails :
    ¬ (resClose (Equiv.swap 0 1) 0 1 + resClose (Equiv.swap 0 1) 1 0 ≤ 2) := by
  rw [resClose_swap]; decide

/-! #### Exponent bookkeeping: `M + 2S + d = E = 4T + 2` -/

/-- Ordinary edges, and both three-cycle edges: `M + 2S = 4T`, then residual demand `d = 2`. -/
theorem exponent_ordinary (T : ℕ) : 2 * T + 2 * T + 2 = 4 * T + 2 := by ring

/-- The repaired transposition seam (`T = S + 1`): `M + 2S = 4T - 2`, then `d = 4`. -/
theorem exponent_closing_repaired (S : ℕ) :
    2 * S + 2 * (S + 1) + 4 = 4 * (S + 1) + 2 := by ring

/-! #### The trace of the closed transfer product — handoff (5.4) at `z = 2`

`tr((J+I)^{M-1}(J+P_σ)) = 3 γ_M + f = 4^M + f - 1`, which is `Σ_a 2^{h(a)}` of (5.4)/(2.3).
Written as an explicit diagonal sum (the repo does not import `Matrix.trace`) and, in the second
form, without `ℕ`-subtraction, since `f = 0` for a three-cycle. -/

/-- The diagonal sum of the master product: `3 γ_{s+1} + fix σ`. -/
theorem sum_diag_onesPlus_pow_mul_onesPerm (s : ℕ) (σ : Equiv.Perm (Fin 3)) :
    ∑ i, (onesPlus ^ s * onesPerm σ) i i
      = 3 * gammaPlus (s + 1) + (univ.filter fun c : Fin 3 => σ c = c).card := by
  have h1 : ∑ i : Fin 3, (if i = σ i then 1 else 0)
      = (univ.filter fun c : Fin 3 => σ c = c).card := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun i _ => by simp [eq_comm]
  simp only [onesPlus_pow_mul_onesPerm]
  rw [Finset.sum_add_distrib, h1]
  simp [mul_comm]

/-- **(5.4) at `z = 2`**: `Σ_a 2^{h(a)} = tr((J+I)^{M-1}(J+P_σ)) = 4 ^ M + f - 1`, stated as
`tr + 1 = 4 ^ M + f` so that no `ℕ`-subtraction occurs (`f = 0` for a three-cycle). -/
theorem sum_diag_onesPlus_pow_mul_onesPerm_closed (M : ℕ) (hM : 1 ≤ M)
    (σ : Equiv.Perm (Fin 3)) :
    (∑ i, (onesPlus ^ (M - 1) * onesPerm σ) i i) + 1
      = 4 ^ M + (univ.filter fun c : Fin 3 => σ c = c).card := by
  obtain ⟨M, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  rw [Nat.add_sub_cancel, sum_diag_onesPlus_pow_mul_onesPerm]
  have := three_mul_gammaPlus_add_one (M + 1)
  omega

/-! #### The transfer-product form of the two pair marginals

These are the same splits as `pairOrdinary_decomp` / `pairClosing_decomp`, but with the
"rest of the cycle" factor written as the actual transfer product rather than an abstract `T`,
so the cut/closed identities of (b) are what supplies `T = γ_{M-1}`.  In both, `T = γ_{M-1}`:
the ordinary edge leaves `M - 2` ordinary transfers and the σ-seam (exponent `s = M - 2`,
constant `γ_{s+1}`), the closing edge leaves `M - 1` ordinary transfers (exponent `s = M - 1`,
constant `γ_s`). -/

/-- **Ordinary pair marginal.**  `own edge (J+I)(i,j)` times `rest of cycle (γ_{s+1}·J + P_σ)(j,i)`,
plus the constant-word correction of (5.3), splits as base `(2T, T)` with `T = γ_{s+1}` plus
`resOrd σ`. -/
theorem pairOrdinary_of_transfer (s : ℕ) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    onesPlus i j * (onesPlus ^ s * onesPerm σ) j i + (if i = j ∧ σ i ≠ i then 1 else 0)
      = (if i = j then 2 * gammaPlus (s + 1) else gammaPlus (s + 1)) + resOrd σ i j := by
  rw [onesPlus_apply, onesPlus_pow_mul_onesPerm]
  exact pairOrdinary_decomp (gammaPlus (s + 1)) σ i j

/-- **Closing pair marginal, aligned coordinates, naive base `(2T, T)`** with `T = γ_s`.
Alignment is the substitution `j ↦ σ j` on the second index, which is why the own-edge factor
`(J + P_σ)(i, σ j)` collapses to `[i = j] ↦ 2` and the correction moves to `i = σ j`. -/
theorem pairClosing_of_transfer (s : ℕ) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    onesPerm σ i (σ j) * (onesPlus ^ s) (σ j) i + (if i = σ j ∧ σ i ≠ i then 1 else 0)
      = (if i = j then 2 * gammaPlus s else gammaPlus s) + resClose σ i j := by
  have hown : onesPerm σ i (σ j) = if i = j then 2 else 1 := by
    rw [onesPerm_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hrest : (onesPlus ^ s) (σ j) i = gammaPlus s + (if i = σ j then 1 else 0) := by
    rw [onesPlus_pow_apply]
    by_cases h : i = σ j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hown, hrest]
  exact pairClosing_decomp (gammaPlus s) σ i j

/-- **Closing pair marginal against the repaired base `(2T - 2, T)`**, `T = γ_{s+1} = 4γ_s + 1`,
so `2T - 2 = 2 · (4γ_s)` stays in `ℕ`.  Residual `resCloseRepaired σ`, demand `d = 4`. -/
theorem pairClosing_of_transfer_repaired (s : ℕ) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    onesPerm σ i (σ j) * (onesPlus ^ (s + 1)) (σ j) i + (if i = σ j ∧ σ i ≠ i then 1 else 0)
      = (if i = j then 2 * (4 * gammaPlus s) else 4 * gammaPlus s + 1)
        + resCloseRepaired σ i j := by
  have hown : onesPerm σ i (σ j) = if i = j then 2 else 1 := by
    rw [onesPerm_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hrest : (onesPlus ^ (s + 1)) (σ j) i
      = (4 * gammaPlus s + 1) + (if i = σ j then 1 else 0) := by
    rw [onesPlus_pow_apply, gammaPlus_succ]
    by_cases h : i = σ j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hown, hrest]
  exact pairClosing_decomp_repaired (4 * gammaPlus s) σ i j

/-! #### The remaining (5.8) side conditions, for every `σ` -/

theorem resClose_rowSum (σ : Equiv.Perm (Fin 3)) (i : Fin 3) : ∑ j, resClose σ i j = 2 := by
  have hc : ∀ j : Fin 3, (i = σ j) ↔ (σ.symm i = j) := by
    intro j
    constructor
    · rintro rfl; exact σ.symm_apply_apply j
    · rintro rfl; exact (σ.apply_symm_apply i).symm
  simp only [resClose, Matrix.of_apply, hc]
  simp

theorem resClose_colSum (σ : Equiv.Perm (Fin 3)) (j : Fin 3) : ∑ i, resClose σ i j = 2 := by
  simp [resClose]

theorem resCloseRepaired_rowSum (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ∑ j, resCloseRepaired σ i j = 4 := by
  have h : ∀ j, resCloseRepaired σ i j = resClose σ i j + 2 * (if i = j then 1 else 0) := by
    intro j; simp [resCloseRepaired, resClose]
  simp only [h]
  rw [Finset.sum_add_distrib, resClose_rowSum]
  simp

theorem resCloseRepaired_colSum (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    ∑ i, resCloseRepaired σ i j = 4 := by
  have h : ∀ i, resCloseRepaired σ i j = resClose σ i j + 2 * (if i = j then 1 else 0) := by
    intro i; simp [resCloseRepaired, resClose]
  simp only [h]
  rw [Finset.sum_add_distrib, resClose_colSum]
  simp

/-- Entry bound of (5.8) for the ordinary residual: `D i j ≤ d = 2`. -/
theorem resOrd_le (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) : resOrd σ i j ≤ 2 := by
  simp only [resOrd, Matrix.of_apply]; split <;> split <;> simp

/-- Entry bound of (5.8) for the naive closing residual: `D i j ≤ d = 2`. -/
theorem resClose_le (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) : resClose σ i j ≤ 2 := by
  simp only [resClose, Matrix.of_apply]; split <;> simp

/-- Entry bound of (5.8) for the repaired closing residual: `D i j ≤ d = 4`. -/
theorem resCloseRepaired_le (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    resCloseRepaired σ i j ≤ 4 := by
  simp only [resCloseRepaired, Matrix.of_apply]; split <;> split <;> simp

/-- **The repaired closing residual always satisfies (5.8)**, for every holonomy `σ` — this is
what the repair buys, and it needs no hypothesis on `σ`. -/
theorem resCloseRepaired_hall (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) (h : i ≠ j) :
    resCloseRepaired σ i j + resCloseRepaired σ j i ≤ 4 := by
  simp only [resCloseRepaired, Matrix.of_apply, if_neg h, if_neg (Ne.symm h)]
  split <;> split <;> simp

/-- **Exactly when the naive closing base survives (5.8)**: the seam pair `(i, j)` violates it
precisely when `σ` swaps `i` and `j`.  Hence any `σ` with no 2-cycle — the identity and the two
three-cycles — needs no repair. -/
theorem resClose_hall_of_no_two_cycle (σ : Equiv.Perm (Fin 3))
    (hσ : ∀ c : Fin 3, σ (σ c) = c → σ c = c) (i j : Fin 3) (h : i ≠ j) :
    resClose σ i j + resClose σ j i ≤ 2 := by
  simp only [resClose, Matrix.of_apply]
  by_cases h1 : i = σ j
  · have h2 : ¬ (j = σ i) := by
      intro h2
      have hjj : σ (σ j) = j := by rw [← h1, ← h2]
      exact h (h1.trans (hσ j hjj))
    rw [if_pos h1, if_neg h2]
  · rw [if_neg h1]
    split <;> norm_num

theorem threeCycle_no_two_cycle (c : Fin 3) :
    threeCycle (threeCycle c) = c → threeCycle c = c := by
  revert c; decide

/-- The three-cycle closing residual satisfies (5.8) with `d = 2`, from the general criterion. -/
theorem resClose_threeCycle_hall' (i j : Fin 3) (h : i ≠ j) :
    resClose threeCycle i j + resClose threeCycle j i ≤ 2 :=
  resClose_hall_of_no_two_cycle threeCycle threeCycle_no_two_cycle i j h

end ListColoring
