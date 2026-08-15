/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.TransferMatrix

/-!
# The bare cycle pair bound: case analysis (UM-106)

The single-root bounds of handoff §6.3 over the transfer-matrix model: `Ts` the list of
surviving-label sets along the relabelled path (`n - 1` entries for an `n`-cycle, `n` even),
`P` the inverse completion of the closing partial injection, `dom` its domain.

* undefined roots carry the full row sum, at least `q^{n-1} = A + (α ≥ 2)`;
* fixed roots carry at least the fixed base `A = (k-1)·β`;
* twisted roots carry at least the moved base `A - 1`, plus their leave/entry corrections
  when the placement is not rigid;
* rigid twisted roots donate at least `k - 2` twice to any other root's count.
-/

namespace ListColoring

open Matrix

variable {k : ℕ}

/-- The root count in the matrix model: deletion at `P⁻¹ c` for defined roots, the full row
sum otherwise. -/
def rootCount (Ts : List (Finset (Fin k))) (P : Equiv.Perm (Fin k)) (dom : Finset (Fin k))
    (c : Fin k) : ℕ :=
  if c ∈ dom then (transferProd Ts * offPerm P) c c
  else ∑ b, transferProd Ts c b

/-- The uniform normalizer in the matrix model. -/
def uniformA (k n : ℕ) : ℕ := (k - 1) * beta k (n - 1)

section SingleRoot

/-- **Undefined roots**: the full row sum clears `A + (k - 2)`. -/
theorem rootCount_undef (hk : 4 ≤ k) {Ts : List (Finset (Fin k))} {P : Equiv.Perm (Fin k)}
    {dom : Finset (Fin k)} {c : Fin k} (hc : c ∉ dom) {n : ℕ} (hn : 4 ≤ n)
    (hlen : Ts.length = n - 1) :
    uniformA k n + (k - 2) ≤ rootCount Ts P dom c := by
  rw [rootCount, if_neg hc]
  have hpure : ∀ b, (offDiag k ^ Ts.length) c b ≤ transferProd Ts c b :=
    fun b => offDiag_pow_le_transferProd Ts c b
  have hflip : ∀ b : Fin k,
      (if c = b then alpha k Ts.length else beta k Ts.length)
        = (if b = c then alpha k Ts.length else beta k Ts.length) := by
    intro b
    by_cases h : c = b
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  calc uniformA k n + (k - 2)
      ≤ alpha k (n - 1) + (k - 1) * beta k (n - 1) := by
        rw [uniformA]
        have := alpha_ge (show 3 ≤ k by omega) (s := n - 1) (by omega)
        omega
    _ = alpha k Ts.length + (k - 1) * beta k Ts.length := by rw [hlen]
    _ = ∑ b, (offDiag k ^ Ts.length) c b := by
        rw [Finset.sum_congr rfl
          (fun b _ => (offDiag_pow_apply (show 1 ≤ k by omega) Ts.length c b).trans (hflip b))]
        rw [sum_ite_single, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
    _ ≤ ∑ b, transferProd Ts c b := Finset.sum_le_sum fun b _ => hpure b

/-- **Fixed roots**: the diagonal clears the fixed base `A`. -/
theorem rootCount_fixed (hk : 4 ≤ k) {Ts : List (Finset (Fin k))} {P : Equiv.Perm (Fin k)}
    {dom : Finset (Fin k)} {c : Fin k} (hc : c ∈ dom) (hfix : P.symm c = c) {n : ℕ}
    (hn : 4 ≤ n) (hlen : Ts.length = n - 1) :
    uniformA k n ≤ rootCount Ts P dom c := by
  rw [rootCount, if_pos hc]
  have h1 : uniformA k n = ((offDiag k ^ Ts.length) * offPerm P) c c := by
    rw [base_diag_fixed (show 1 ≤ k by omega) P hfix, uniformA, hlen]
  rw [h1]
  exact matmul_le_matmul (offDiag_pow_le_transferProd Ts) (fun _ _ => le_refl _) c c


/-- The moved diagonal value clears `k - 2` for `s ≥ 1`. -/
theorem moved_val_ge {s : ℕ} (hk : 3 ≤ k) (hs : 1 ≤ s) :
    k - 2 ≤ alpha k s + (k - 2) * beta k s := by
  have h := one_le_beta hk s hs
  have h2 : k - 2 ≤ (k - 2) * beta k s := by
    calc k - 2 = (k - 2) * 1 := by omega
      _ ≤ (k - 2) * beta k s := Nat.mul_le_mul_left _ h
  omega

/-- **Any defined root clears the moved base** (`A - 1`), even cycles. -/
theorem rootCount_defined_base (hk : 4 ≤ k) {Ts : List (Finset (Fin k))}
    {P : Equiv.Perm (Fin k)} {dom : Finset (Fin k)} {c : Fin k} (hc : c ∈ dom) {n : ℕ}
    (hn : 4 ≤ n) (hne : Even n) (hlen : Ts.length = n - 1) :
    alpha k (n - 1) + (k - 2) * beta k (n - 1) ≤ rootCount Ts P dom c := by
  have halt : beta k (n - 1) = alpha k (n - 1) + 1 :=
    (beta_alternation (show 2 ≤ k by omega) (n - 1)).1
      (Nat.Even.sub_odd (by omega) hne odd_one)
  rw [rootCount, if_pos hc]
  by_cases hfix : P.symm c = c
  · have h1 : ((offDiag k ^ Ts.length) * offPerm P) c c = (k - 1) * beta k (n - 1) := by
      rw [base_diag_fixed (show 1 ≤ k by omega) P hfix, hlen]
    have h2 : alpha k (n - 1) + (k - 2) * beta k (n - 1) ≤ (k - 1) * beta k (n - 1) := by
      have hsplitk : (k - 1) * beta k (n - 1)
          = beta k (n - 1) + (k - 2) * beta k (n - 1) := by
        rw [show k - 1 = 1 + (k - 2) from by omega, Nat.add_mul, Nat.one_mul]
      rw [hsplitk]
      omega
    refine le_trans h2 (le_trans (le_of_eq h1.symm) ?_)
    exact matmul_le_matmul (offDiag_pow_le_transferProd Ts) (fun _ _ => le_refl _) c c
  · have h1 : ((offDiag k ^ Ts.length) * offPerm P) c c
        = alpha k (n - 1) + (k - 2) * beta k (n - 1) := by
      rw [base_diag_moved (show 1 ≤ k by omega) P hfix, hlen]
    refine le_trans (le_of_eq h1.symm) ?_
    exact matmul_le_matmul (offDiag_pow_le_transferProd Ts) (fun _ _ => le_refl _) c c

/-- **The twisted master bound**: the moved base plus the leave and entry corrections. -/
theorem rootCount_twisted (hk : 4 ≤ k) {P : Equiv.Perm (Fin k)}
    {dom : Finset (Fin k)} {c : Fin k} (hc : c ∈ dom) (htw : P.symm c ≠ c) {n : ℕ}
    (hn : 4 ≤ n)
    (Ts₁ : List (Finset (Fin k))) (T : Finset (Fin k)) (Ts₂ : List (Finset (Fin k)))
    (T' : Finset (Fin k)) (Ts₃ : List (Finset (Fin k)))
    (hlen : (Ts₁ ++ T :: (Ts₂ ++ T' :: Ts₃)).length = n - 1)
    (hcT : c ∈ T) (hmT' : P.symm c ∈ T') :
    (alpha k (n - 1) + (k - 2) * beta k (n - 1))
      + beta k (Ts₁.length + 1 + Ts₂.length) * ((k - 1) * beta k Ts₃.length)
      + alpha k Ts₁.length *
          (alpha k (Ts₂ ++ T' :: Ts₃).length + (k - 2) * beta k (Ts₂ ++ T' :: Ts₃).length)
      ≤ rootCount (Ts₁ ++ T :: (Ts₂ ++ T' :: Ts₃)) P dom c := by
  rw [rootCount, if_pos hc]
  have hmono := matmul_le_matmul (le_transferProd_two Ts₁ T Ts₂ T' Ts₃)
    (fun (i j : Fin k) => le_refl (offPerm P i j)) c c
  refine le_trans ?_ hmono
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_apply, Matrix.add_apply]
  refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
  · -- the pure base
    have h := offDiag_pow_mulOffPerm_apply (show 1 ≤ k by omega)
      ((Ts₁ ++ T :: (Ts₂ ++ T' :: Ts₃)).length) P c c
    rw [if_neg (fun h' : c = P.symm c => htw h'.symm)] at h
    rw [← hlen]
    exact le_of_eq h.symm
  · -- the entry correction at `T'`
    have hcg := corr_diag_ge (Ts₁.length + 1 + Ts₂.length) T'
      ((offDiag k ^ Ts₃.length) * offPerm P) c (P.symm c) hmT'
    rw [offDiag_pow_apply (show 1 ≤ k by omega),
      if_neg (fun h' : c = P.symm c => htw h'.symm),
      offDiag_pow_mulOffPerm_apply (show 1 ≤ k by omega), if_pos rfl] at hcg
    rw [Matrix.mul_assoc]
    exact hcg
  · -- the leave correction at `T`
    have hcg := corr_diag_ge Ts₁.length T
      ((offDiag k ^ (Ts₂ ++ T' :: Ts₃).length) * offPerm P) c c hcT
    rw [offDiag_pow_apply (show 1 ≤ k by omega), if_pos rfl,
      offDiag_pow_mulOffPerm_apply (show 1 ≤ k by omega),
      if_neg (fun h' : c = P.symm c => htw h'.symm)] at hcg
    rw [Matrix.mul_assoc]
    exact hcg


/-- **The donation form**: any defined root's count dominates its base plus the two
corrections of another root's thread. -/
theorem rootCount_donation (hk : 4 ≤ k) {P : Equiv.Perm (Fin k)}
    {dom : Finset (Fin k)} {d : Fin k} (hd : d ∈ dom)
    (Ts₁ : List (Finset (Fin k))) (T : Finset (Fin k)) (Ts₂ : List (Finset (Fin k)))
    (T' : Finset (Fin k)) (Ts₃ : List (Finset (Fin k))) :
    (((offDiag k ^ (Ts₁ ++ T :: (Ts₂ ++ T' :: Ts₃)).length) * offPerm P) d d)
      + (((offDiag k ^ (Ts₁.length + 1 + Ts₂.length)) * diagInd T' *
          (offDiag k ^ Ts₃.length)) * offPerm P) d d
      + (((offDiag k ^ Ts₁.length) * diagInd T *
          (offDiag k ^ (Ts₂ ++ T' :: Ts₃).length)) * offPerm P) d d
      ≤ rootCount (Ts₁ ++ T :: (Ts₂ ++ T' :: Ts₃)) P dom d := by
  rw [rootCount, if_pos hd]
  have hmono := matmul_le_matmul (le_transferProd_two Ts₁ T Ts₂ T' Ts₃)
    (fun (i j : Fin k) => le_refl (offPerm P i j)) d d
  refine le_trans (le_of_eq ?_) hmono
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.add_apply, Matrix.add_apply]

end SingleRoot

end ListColoring
