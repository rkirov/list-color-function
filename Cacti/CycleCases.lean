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

end SingleRoot

end ListColoring
