/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Data.Matrix.Basic
import Cacti.Defs

/-!
# Transfer-matrix arithmetic for the bare cycle pair bound

The graph-free layer of UM-106 (handoff §6.2): the diagonal/off-diagonal entries `α_s`, `β_s`
of `(J - I)^s` over a `k`-element index set, by their mutual recursion

`α_{s+1} = (k-1)·β_s`,  `β_{s+1} = α_s + (k-2)·β_s`,

with the row-sum identity `α_s + (k-1)·β_s = q^s` (`q = k - 1`), the alternation
`β_s = α_s ± 1`, and the elementary bounds (2.10) that the case analysis consumes.
-/

namespace ListColoring

mutual
/-- The diagonal entry of `(J - I)^s` on `k` indices. -/
def alpha (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | s + 1 => (k - 1) * beta k s

/-- The off-diagonal entry of `(J - I)^s` on `k` indices. -/
def beta (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 => alpha k s + (k - 2) * beta k s
end

@[simp] theorem alpha_zero (k : ℕ) : alpha k 0 = 1 := by rw [alpha]
@[simp] theorem beta_zero (k : ℕ) : beta k 0 = 0 := by rw [beta]
theorem alpha_succ (k s : ℕ) : alpha k (s + 1) = (k - 1) * beta k s := by rw [alpha]
theorem beta_succ (k s : ℕ) : beta k (s + 1) = alpha k s + (k - 2) * beta k s := by rw [beta]

@[simp] theorem alpha_one (k : ℕ) : alpha k 1 = 0 := by
  rw [alpha_succ, beta_zero, Nat.mul_zero]
@[simp] theorem beta_one (k : ℕ) : beta k 1 = 1 := by
  rw [beta_succ, alpha_zero, beta_zero, Nat.mul_zero]

/-- The row-sum identity: `α_s + (k-1)·β_s = (k-1)^s`. -/
theorem alpha_add_beta {k : ℕ} (hk : 2 ≤ k) : ∀ s, alpha k s + (k - 1) * beta k s = (k - 1) ^ s := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [h1] at ih
    rw [alpha_succ, beta_succ, h1, h2, pow_succ, ← ih]
    ring

/-- The alternation: `β` and `α` differ by exactly one, in alternating directions. -/
theorem beta_alternation {k : ℕ} (hk : 2 ≤ k) :
    ∀ s, (Odd s → beta k s = alpha k s + 1) ∧ (Even s → alpha k s = beta k s + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 2 - 2 = m := by omega
  intro s
  induction s with
  | zero =>
    refine ⟨fun h => absurd h (by simp), fun _ => by simp⟩
  | succ s ih =>
    obtain ⟨ho, he⟩ := ih
    constructor
    · intro hodd
      have hs : Even s := by
        rcases Nat.even_or_odd s with h | h
        · exact h
        · exact absurd hodd (by simp [Nat.odd_add_one, Nat.not_even_iff_odd.mpr h])
      rw [alpha_succ, beta_succ, he hs, h1, h2]
      ring
    · intro heven
      have hs : Odd s := by
        rcases Nat.even_or_odd s with h | h
        · exact absurd heven (by simp [Nat.even_add_one, Nat.not_odd_iff_even.mpr h])
        · exact h
      rw [alpha_succ, beta_succ, ho hs, h1, h2]
      ring


/-- `β_s ≥ 1` for `s ≥ 1`. -/
theorem one_le_beta {k : ℕ} (hk : 3 ≤ k) : ∀ s, 1 ≤ s → 1 ≤ beta k s
  | 1, _ => by simp
  | s + 2, _ => by
    rw [beta_succ]
    have h := one_le_beta hk (s + 1) (by omega)
    have h2 : 1 ≤ k - 2 := by omega
    calc 1 ≤ (k - 2) * beta k (s + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      _ ≤ _ := Nat.le_add_left _ _

/-- `α_s ≥ k - 2` for `s ≥ 2` (the bound (2.10), first half for `α`). -/
theorem alpha_ge {k : ℕ} (hk : 3 ≤ k) {s : ℕ} (hs : 2 ≤ s) : k - 2 ≤ alpha k s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
  rw [alpha_succ]
  calc k - 2 ≤ (k - 1) * 1 := by omega
    _ ≤ (k - 1) * beta k (t + 1) := Nat.mul_le_mul_left _ (one_le_beta hk _ (by omega))

/-- `β_s ≥ k - 2` for `s ≥ 2`. -/
theorem beta_ge {k : ℕ} (hk : 3 ≤ k) {s : ℕ} (hs : 2 ≤ s) : k - 2 ≤ beta k s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
  rw [beta_succ]
  calc k - 2 ≤ (k - 2) * 1 := by omega
    _ ≤ (k - 2) * beta k (t + 1) := Nat.mul_le_mul_left _ (one_le_beta hk _ (by omega))
    _ ≤ _ := Nat.le_add_left _ _

/-- The complementary bound: `α_s + (k - 2) ≤ (k-1)^s` for `s ≥ 1`. -/
theorem alpha_add_le {k : ℕ} (hk : 3 ≤ k) {s : ℕ} (hs : 1 ≤ s) :
    alpha k s + (k - 2) ≤ (k - 1) ^ s := by
  rw [← alpha_add_beta (by omega : 2 ≤ k) s]
  have h := one_le_beta hk s hs
  have : k - 2 ≤ (k - 1) * beta k s := by
    calc k - 2 ≤ (k - 1) * 1 := by omega
      _ ≤ (k - 1) * beta k s := Nat.mul_le_mul_left _ h
  omega

/-- The complementary bound: `β_s + (k - 2) ≤ (k-1)^s` for `s ≥ 1`. -/
theorem beta_add_le {k : ℕ} (hk : 3 ≤ k) {s : ℕ} (hs : 1 ≤ s) :
    beta k s + (k - 2) ≤ (k - 1) ^ s := by
  rw [← alpha_add_beta (by omega : 2 ≤ k) s]
  -- `(k-1)·β = β + (k-2)·β` and `α + (k-2)·β ≥ k - 2` from `β_s ≥ 1`
  have h := one_le_beta hk s hs
  have h1 : (k - 1) * beta k s = beta k s + (k - 2) * beta k s := by
    have : k - 1 = 1 + (k - 2) := by omega
    rw [this]
    ring
  have h2 : k - 2 ≤ alpha k s + (k - 2) * beta k s := by
    calc k - 2 ≤ (k - 2) * 1 := by omega
      _ ≤ (k - 2) * beta k s := Nat.mul_le_mul_left _ h
      _ ≤ _ := Nat.le_add_left _ _
  omega


section Matrices

open Matrix

variable {k : ℕ}

/-- The all-ones-off-diagonal matrix `J - I`. -/
def offDiag (k : ℕ) : Matrix (Fin k) (Fin k) ℕ :=
  Matrix.of fun i j => if i = j then 0 else 1

/-- The diagonal indicator of a set of indices. -/
def diagInd (T : Finset (Fin k)) : Matrix (Fin k) (Fin k) ℕ :=
  Matrix.of fun i j => if i = j ∧ i ∈ T then 1 else 0

/-- `J - P` for a permutation `P`, entrywise. -/
def offPerm (P : Equiv.Perm (Fin k)) : Matrix (Fin k) (Fin k) ℕ :=
  Matrix.of fun b c => if P b = c then 0 else 1

/-- Summing an `if · = i` pattern over `Fin k`. -/
theorem sum_ite_single {i : Fin k} (a : ℕ) (b : Fin k → ℕ) :
    (∑ e : Fin k, if e = i then a else b e)
      = a + ∑ e ∈ Finset.univ.erase i, b e := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl]
  congr 1
  exact Finset.sum_congr rfl fun e he => if_neg (Finset.ne_of_mem_erase he)

/-- The entries of `(J-I)^s` are `α` on the diagonal and `β` off it. -/
theorem offDiag_pow_apply (hk : 1 ≤ k) :
    ∀ (s : ℕ) (i j : Fin k), (offDiag k ^ s) i j = if i = j then alpha k s else beta k s := by
  intro s
  induction s with
  | zero =>
    intro i j
    by_cases hij : i = j
    · rw [if_pos hij, hij, pow_zero, alpha_zero, Matrix.one_apply_eq]
    · rw [if_neg hij, pow_zero, beta_zero, Matrix.one_apply_ne hij]
  | succ s ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply]
    have hterm : ∀ e : Fin k,
        (offDiag k) i e * (offDiag k ^ s) e j
          = (if e = i then 0 else (if e = j then alpha k s else beta k s)) := by
      intro e
      rw [ih e j]
      show (if i = e then 0 else 1) * _ = _
      by_cases he : e = i
      · rw [if_pos he.symm, if_pos he, Nat.zero_mul]
      · rw [if_neg (fun h => he h.symm), if_neg he, Nat.one_mul]
    rw [Finset.sum_congr rfl (fun e _ => hterm e), sum_ite_single]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, alpha_succ]
      have hrest : ∀ e ∈ Finset.univ.erase i,
          (if e = i then alpha k s else beta k s) = beta k s :=
        fun e he => if_neg (Finset.ne_of_mem_erase he)
      rw [Finset.sum_congr rfl hrest, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, Nat.zero_add]
    · rw [if_neg hij, beta_succ]
      have hji : j ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨fun h => hij h.symm, Finset.mem_univ j⟩
      rw [← Finset.add_sum_erase _ _ hji, if_pos rfl]
      have hrest : ∀ e ∈ (Finset.univ.erase i).erase j,
          (if e = j then alpha k s else beta k s) = beta k s :=
        fun e he => if_neg (Finset.ne_of_mem_erase he)
      rw [Finset.sum_congr rfl hrest, Finset.sum_const,
        Finset.card_erase_of_mem hji, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.zero_add]
      have h11 : k - 1 - 1 = k - 2 := by omega
      rw [h11]

end Matrices

end ListColoring
