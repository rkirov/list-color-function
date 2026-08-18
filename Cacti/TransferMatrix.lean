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
theorem alpha_add_beta {k : ℕ} (hk : 2 ≤ k) :
    ∀ s, alpha k s + (k - 1) * beta k s = (k - 1) ^ s := by
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


section Expansion

open Matrix

variable {k : ℕ}

/-- Entrywise matrix inequality over `ℕ` is preserved by multiplication. -/
theorem matmul_le_matmul {A A' B B' : Matrix (Fin k) (Fin k) ℕ}
    (hA : ∀ i j, A i j ≤ A' i j) (hB : ∀ i j, B i j ≤ B' i j) :
    ∀ i j, (A * B) i j ≤ (A' * B') i j := by
  intro i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_le_sum fun e _ => Nat.mul_le_mul (hA i e) (hB e j)

/-- The transfer product of a list of index sets. -/
def transferProd (Ts : List (Finset (Fin k))) : Matrix (Fin k) (Fin k) ℕ :=
  (Ts.map (fun T => offDiag k + diagInd T)).prod

@[simp] theorem transferProd_nil : transferProd ([] : List (Finset (Fin k))) = 1 := rfl

theorem transferProd_cons (T : Finset (Fin k)) (Ts : List (Finset (Fin k))) :
    transferProd (T :: Ts) = (offDiag k + diagInd T) * transferProd Ts := by
  rw [transferProd, List.map_cons, List.prod_cons, transferProd]

theorem transferProd_append (Ts₁ Ts₂ : List (Finset (Fin k))) :
    transferProd (Ts₁ ++ Ts₂) = transferProd Ts₁ * transferProd Ts₂ := by
  rw [transferProd, List.map_append, List.prod_append, transferProd, transferProd]

/-- The empty gate is the zero matrix. -/
@[simp] theorem diagInd_empty : diagInd (∅ : Finset (Fin k)) = 0 := by
  ext i j
  simp [diagInd]

/-- With no surviving labels anywhere, the transfer product is the pure power. -/
theorem transferProd_replicate_empty (n : ℕ) :
    transferProd (List.replicate n (∅ : Finset (Fin k))) = offDiag k ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, transferProd_cons, ih, diagInd_empty, add_zero, pow_succ']

/-- The pure part: `(J-I)^len ≤ transferProd`. -/
theorem offDiag_pow_le_transferProd (Ts : List (Finset (Fin k))) :
    ∀ i j, (offDiag k ^ Ts.length) i j ≤ transferProd Ts i j := by
  induction Ts with
  | nil => intro i j; simp
  | cons T Ts ih =>
    intro i j
    rw [transferProd_cons, List.length_cons, pow_succ']
    refine matmul_le_matmul (fun i' j' => ?_) ih i j
    show offDiag k i' j' ≤ (offDiag k + diagInd T) i' j'
    exact Nat.le_add_right _ _

/-- **One retained correction**: the pure power plus one diagonal insertion. -/
theorem le_transferProd_one (Ts₁ : List (Finset (Fin k))) (T : Finset (Fin k))
    (Ts₂ : List (Finset (Fin k))) :
    ∀ i j, ((offDiag k ^ (Ts₁ ++ T :: Ts₂).length) +
        (offDiag k ^ Ts₁.length) * diagInd T * (offDiag k ^ Ts₂.length)) i j ≤
      transferProd (Ts₁ ++ T :: Ts₂) i j := by
  intro i j
  rw [transferProd_append, transferProd_cons]
  have hexp : transferProd Ts₁ * ((offDiag k + diagInd T) * transferProd Ts₂)
      = transferProd Ts₁ * (offDiag k * transferProd Ts₂) +
        transferProd Ts₁ * (diagInd T * transferProd Ts₂) := by
    rw [Matrix.add_mul, Matrix.mul_add]
  rw [hexp]
  rw [Matrix.add_apply, Matrix.add_apply]
  refine Nat.add_le_add ?_ ?_
  · have h1 : ∀ i j, (offDiag k ^ (Ts₁ ++ T :: Ts₂).length) i j
        ≤ (transferProd Ts₁ * (offDiag k * transferProd Ts₂)) i j := by
      intro i j
      have hlen : (Ts₁ ++ T :: Ts₂).length = Ts₁.length + (1 + Ts₂.length) := by
        simp [List.length_append]
        omega
      rw [hlen, pow_add, pow_add, pow_one]
      exact matmul_le_matmul (offDiag_pow_le_transferProd Ts₁)
        (matmul_le_matmul (fun _ _ => le_refl _) (offDiag_pow_le_transferProd Ts₂)) i j
    exact h1 i j
  · have h2 : (offDiag k ^ Ts₁.length) * diagInd T * (offDiag k ^ Ts₂.length)
        = (offDiag k ^ Ts₁.length) * (diagInd T * (offDiag k ^ Ts₂.length)) := by
      rw [Matrix.mul_assoc]
    rw [h2]
    exact matmul_le_matmul (offDiag_pow_le_transferProd Ts₁)
      (matmul_le_matmul (fun _ _ => le_refl _) (offDiag_pow_le_transferProd Ts₂)) i j


/-- **Two retained corrections**: the pure power plus two diagonal insertions. -/
theorem le_transferProd_two (Ts₁ : List (Finset (Fin k))) (T : Finset (Fin k))
    (Ts₂ : List (Finset (Fin k))) (T' : Finset (Fin k)) (Ts₃ : List (Finset (Fin k))) :
    ∀ i j, ((offDiag k ^ (Ts₁ ++ T :: (Ts₂ ++ T' :: Ts₃)).length)
        + (offDiag k ^ (Ts₁.length + 1 + Ts₂.length)) * diagInd T' * (offDiag k ^ Ts₃.length)
        + (offDiag k ^ Ts₁.length) * diagInd T *
            (offDiag k ^ (Ts₂ ++ T' :: Ts₃).length)) i j ≤
      transferProd (Ts₁ ++ T :: (Ts₂ ++ T' :: Ts₃)) i j := by
  intro i j
  rw [transferProd_append, transferProd_cons]
  have hexp : transferProd Ts₁ * ((offDiag k + diagInd T) * transferProd (Ts₂ ++ T' :: Ts₃))
      = transferProd Ts₁ * (offDiag k * transferProd (Ts₂ ++ T' :: Ts₃))
        + transferProd Ts₁ * (diagInd T * transferProd (Ts₂ ++ T' :: Ts₃)) := by
    rw [Matrix.add_mul, Matrix.mul_add]
  rw [hexp, Matrix.add_apply, Matrix.add_apply]
  refine Nat.add_le_add ?_ ?_
  · -- the pure part and the second correction ride inside `P₁ · (E · Q)`
    have hkey : ∀ i' j', ((offDiag k ^ (Ts₁ ++ T :: (Ts₂ ++ T' :: Ts₃)).length)
          + (offDiag k ^ (Ts₁.length + 1 + Ts₂.length)) * diagInd T' *
              (offDiag k ^ Ts₃.length)) i' j'
        ≤ ((offDiag k ^ Ts₁.length) *
            (offDiag k * ((offDiag k ^ (Ts₂ ++ T' :: Ts₃).length)
              + (offDiag k ^ Ts₂.length) * diagInd T' * (offDiag k ^ Ts₃.length)))) i' j' := by
      intro i' j'
      have hda : (offDiag k ^ Ts₁.length) *
          (offDiag k * ((offDiag k ^ (Ts₂ ++ T' :: Ts₃).length)
            + (offDiag k ^ Ts₂.length) * diagInd T' * (offDiag k ^ Ts₃.length)))
          = (offDiag k ^ (Ts₁ ++ T :: (Ts₂ ++ T' :: Ts₃)).length)
            + (offDiag k ^ (Ts₁.length + 1 + Ts₂.length)) * diagInd T' *
                (offDiag k ^ Ts₃.length) := by
        rw [Matrix.mul_add, Matrix.mul_add]
        congr 1
        · have hlen : (Ts₁ ++ T :: (Ts₂ ++ T' :: Ts₃)).length
              = Ts₁.length + (1 + (Ts₂ ++ T' :: Ts₃).length) := by
            simp [List.length_append]
            omega
          rw [hlen, pow_add, pow_add, pow_one]
        · rw [show Ts₁.length + 1 + Ts₂.length = Ts₁.length + (1 + Ts₂.length) from by omega,
            pow_add, pow_add, pow_one]
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      rw [hda]
    refine le_trans (hkey i j) ?_
    exact matmul_le_matmul (offDiag_pow_le_transferProd Ts₁)
      (matmul_le_matmul (fun _ _ => le_refl _) (le_transferProd_one Ts₂ T' Ts₃)) i j
  · rw [Matrix.mul_assoc]
    exact matmul_le_matmul (offDiag_pow_le_transferProd Ts₁)
      (matmul_le_matmul (fun _ _ => le_refl _)
        (offDiag_pow_le_transferProd (Ts₂ ++ T' :: Ts₃))) i j

end Expansion


section OffPermDiag

open Matrix

variable {k : ℕ}

/-- The diagonal of `X · (J - P)`: the row sum away from `P⁻¹` of the index. -/
theorem mulOffPerm_diag (X : Matrix (Fin k) (Fin k) ℕ) (P : Equiv.Perm (Fin k)) (c : Fin k) :
    (X * offPerm P) c c = ∑ b ∈ Finset.univ.erase (P.symm c), X c b := by
  rw [Matrix.mul_apply]
  have hterm : ∀ b, X c b * offPerm P b c = if b = P.symm c then 0 else X c b := by
    intro b
    show X c b * (if P b = c then 0 else 1) = _
    by_cases hb : P b = c
    · rw [if_pos hb, if_pos (by rw [← hb, Equiv.symm_apply_apply]), Nat.mul_zero]
    · rw [if_neg hb, if_neg (fun h => hb (by rw [h, Equiv.apply_symm_apply])), Nat.mul_one]
  rw [Finset.sum_congr rfl (fun b _ => hterm b), sum_ite_single, Nat.zero_add]

/-- The base diagonal at a fixed index (`P⁻¹ c = c`): the value `A = (k-1)·β_{n-1}`. -/
theorem base_diag_fixed {n : ℕ} (hk : 1 ≤ k) (P : Equiv.Perm (Fin k)) {c : Fin k}
    (hc : P.symm c = c) :
    ((offDiag k ^ n) * offPerm P) c c = (k - 1) * beta k n := by
  rw [mulOffPerm_diag, hc]
  rw [Finset.sum_congr rfl (fun b hb => by
    rw [offDiag_pow_apply hk n c b, if_neg (fun h => Finset.ne_of_mem_erase hb h.symm)])]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- The base diagonal at a moved index (`P⁻¹ c ≠ c`): the value `α + (k-2)·β`. -/
theorem base_diag_moved {n : ℕ} (hk : 1 ≤ k) (P : Equiv.Perm (Fin k)) {c : Fin k}
    (hc : P.symm c ≠ c) :
    ((offDiag k ^ n) * offPerm P) c c = alpha k n + (k - 2) * beta k n := by
  rw [mulOffPerm_diag]
  have hcmem : c ∈ Finset.univ.erase (P.symm c) :=
    Finset.mem_erase.mpr ⟨fun h => hc h.symm, Finset.mem_univ c⟩
  rw [← Finset.add_sum_erase _ _ hcmem]
  rw [offDiag_pow_apply hk n c c, if_pos rfl]
  congr 1
  rw [Finset.sum_congr rfl (fun b hb => by
    rw [offDiag_pow_apply hk n c b,
      if_neg (fun h => Finset.ne_of_mem_erase hb h.symm)])]
  rw [Finset.sum_const, Finset.card_erase_of_mem hcmem,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  have h11 : k - 1 - 1 = k - 2 := by omega
  rw [h11]

end OffPermDiag


section CorrectionValues

open Matrix

variable {k : ℕ}

/-- The general off-permutation entry: `(X · (J-P)) z c` is the `z`-row sum away from
`P⁻¹ c`. -/
theorem mulOffPerm_apply (X : Matrix (Fin k) (Fin k) ℕ) (P : Equiv.Perm (Fin k))
    (z c : Fin k) :
    (X * offPerm P) z c = ∑ b ∈ Finset.univ.erase (P.symm c), X z b := by
  rw [Matrix.mul_apply]
  have hterm : ∀ b, X z b * offPerm P b c = if b = P.symm c then 0 else X z b := by
    intro b
    show X z b * (if P b = c then 0 else 1) = _
    by_cases hb : P b = c
    · rw [if_pos hb, if_pos (by rw [← hb, Equiv.symm_apply_apply]), Nat.mul_zero]
    · rw [if_neg hb, if_neg (fun h => hb (by rw [h, Equiv.apply_symm_apply])), Nat.mul_one]
  rw [Finset.sum_congr rfl (fun b _ => hterm b), sum_ite_single, Nat.zero_add]

/-- The two values of `((J-I)^s · (J-P)) z c`. -/
theorem offDiag_pow_mulOffPerm_apply (hk : 1 ≤ k) (s : ℕ) (P : Equiv.Perm (Fin k))
    (z c : Fin k) :
    ((offDiag k ^ s) * offPerm P) z c =
      if z = P.symm c then (k - 1) * beta k s else alpha k s + (k - 2) * beta k s := by
  rw [mulOffPerm_apply]
  by_cases hz : z = P.symm c
  · rw [if_pos hz, hz]
    rw [Finset.sum_congr rfl (fun b hb => by
      rw [offDiag_pow_apply hk s _ b, if_neg (fun h => Finset.ne_of_mem_erase hb h.symm)])]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  · rw [if_neg hz]
    have hzmem : z ∈ Finset.univ.erase (P.symm c) :=
      Finset.mem_erase.mpr ⟨hz, Finset.mem_univ z⟩
    rw [← Finset.add_sum_erase _ _ hzmem, offDiag_pow_apply hk s z z, if_pos rfl]
    congr 1
    rw [Finset.sum_congr rfl (fun b hb => by
      rw [offDiag_pow_apply hk s z b,
        if_neg (fun h => Finset.ne_of_mem_erase hb h.symm)])]
    rw [Finset.sum_const, Finset.card_erase_of_mem hzmem,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    have h11 : k - 1 - 1 = k - 2 := by omega
    rw [h11]

/-- Left-multiplication by a diagonal indicator gates the row. -/
theorem diagInd_mul_apply (T : Finset (Fin k)) (X : Matrix (Fin k) (Fin k) ℕ) (z c : Fin k) :
    (diagInd T * X) z c = if z ∈ T then X z c else 0 := by
  rw [Matrix.mul_apply]
  have hterm : ∀ b, diagInd T z b * X b c = if b = z ∧ z ∈ T then X b c else 0 := by
    intro b
    show (if z = b ∧ z ∈ T then 1 else 0) * X b c = _
    by_cases h : z = b ∧ z ∈ T
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2⟩, Nat.one_mul]
    · rw [if_neg h, if_neg (fun hh => h ⟨hh.1.symm, hh.2⟩), Nat.zero_mul]
  rw [Finset.sum_congr rfl (fun b _ => hterm b)]
  by_cases hzT : z ∈ T
  · simp only [hzT, and_true, if_true]
    rw [Finset.sum_ite_eq' Finset.univ z (fun b => X b c), if_pos (Finset.mem_univ z)]
  · simp only [hzT, and_false, if_false]
    exact Finset.sum_const_zero

/-- **One retained slot of a correction**: keep a single index of the diagonal insertion. -/
theorem corr_diag_ge (i₁ : ℕ) (T : Finset (Fin k)) (X : Matrix (Fin k) (Fin k) ℕ)
    (c z : Fin k) (hz : z ∈ T) :
    (offDiag k ^ i₁) c z * X z c ≤ ((offDiag k ^ i₁) * diagInd T * X) c c := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  have hval : (diagInd T * X) z c = X z c := by
    rw [diagInd_mul_apply, if_pos hz]
  calc (offDiag k ^ i₁) c z * X z c
      = (offDiag k ^ i₁) c z * (diagInd T * X) z c := by rw [hval]
    _ ≤ ∑ b, (offDiag k ^ i₁) c b * (diagInd T * X) b c :=
        Finset.single_le_sum (f := fun b => (offDiag k ^ i₁) c b * (diagInd T * X) b c)
          (fun b _ => Nat.zero_le _) (Finset.mem_univ z)

end CorrectionValues

end ListColoring
