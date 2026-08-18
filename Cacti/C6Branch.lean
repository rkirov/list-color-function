/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.EvenSplit

set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# The strict `(2,1)` cone point on an unequal-list two-edge path

`path_strict_pow` (Cacti/PathCone.lean) is stated conditionally on

  `h3 : 729 * X ^ 4 ≤ 4 * (D ^ 2 * O)`,

the strict companion of `path_cone_two_one` (`2^6 * X^4 ≤ D^2 * O`).  This file proves `h3`
whenever the two terminal enumerations differ, i.e. whenever the two terminal lists are not the
same set.  The constant `729/4` is optimal: equality holds at the one-hole pattern
`a = (0,1,2)`, `b = (0,1,*)` with weights `(2,2,1)`.
-/

namespace ListColoring

open Finset

section Strict

variable {Z : Finset ℕ} {x : ℕ → ℕ} {a b : Fin 3 → ℕ}

/-! ## Scalar AM–GM pieces -/

/-- Weighted AM–GM on a pair with masses `(2,1)`: `27 p²q ≤ 4 (p+q)³`, an equality at `p = 2q`.
This is the factor `27/4` of the one-hole certificate. -/
theorem amgm_two_one (p q : ℕ) : 27 * (p ^ 2 * q) ≤ 4 * (p + q) ^ 3 := by
  zify
  nlinarith [sq_nonneg ((p : ℤ) - 2 * q), Int.natCast_nonneg p, Int.natCast_nonneg q,
    mul_nonneg (sq_nonneg ((p : ℤ) - 2 * q)) (by positivity : (0:ℤ) ≤ 4 * (p : ℤ) + q)]

/-- The one-hole polynomial core: with `u₂` the hole colour,
`729 u₀³u₁³u₂² ≤ 4 (u₁+u₂)³(u₀+u₂)³(u₀+u₁)²`.  Sharp at `u₀ = u₁ = 2u₂`. -/
theorem strict_poly (u0 u1 u2 : ℕ) :
    729 * (u0 ^ 3 * u1 ^ 3 * u2 ^ 2) ≤ 4 * ((u1 + u2) ^ 3 * (u0 + u2) ^ 3 * (u0 + u1) ^ 2) := by
  have h1 := amgm_two_one u1 u2
  have h2 := amgm_two_one u0 u2
  have h3 := amgm_two u0 u1
  have hkey : (27 * (u1 ^ 2 * u2)) * ((27 * (u0 ^ 2 * u2)) * (2 ^ 2 * (u0 * u1)))
      ≤ (4 * (u1 + u2) ^ 3) * ((4 * (u0 + u2) ^ 3) * ((u0 + u1) ^ 2)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  have hL : (27 * (u1 ^ 2 * u2)) * ((27 * (u0 ^ 2 * u2)) * (2 ^ 2 * (u0 * u1)))
      = 4 * (729 * (u0 ^ 3 * u1 ^ 3 * u2 ^ 2)) := by ring
  have hR : (4 * (u1 + u2) ^ 3) * ((4 * (u0 + u2) ^ 3) * ((u0 + u1) ^ 2))
      = 4 * (4 * ((u1 + u2) ^ 3 * (u0 + u2) ^ 3 * (u0 + u1) ^ 2)) := by ring
  rw [hL, hR] at hkey
  exact Nat.le_of_mul_le_mul_left hkey (by norm_num)

/-- The one-hole certificate, in the shape the nine cell bounds produce. -/
theorem strict_assemble {u0 u1 u2 d0 d1 d2 e01 e02 e10 e12 e20 e21 : ℕ}
    (hd0 : u1 + u2 ≤ d0) (hd1 : u0 + u2 ≤ d1) (hd2 : u0 + u1 ≤ d2)
    (he01 : u2 ≤ e01) (he02 : u1 + u2 ≤ e02) (he10 : u2 ≤ e10) (he12 : u0 + u2 ≤ e12)
    (he20 : u1 ≤ e20) (he21 : u0 ≤ e21) :
    729 * (u0 * u1 * u2) ^ 4
      ≤ 4 * ((d0 * d1 * d2) ^ 2 * (e01 * e02 * (e10 * e12) * (e20 * e21))) := by
  have hstep : 729 * (u0 * u1 * u2) ^ 4
      ≤ 4 * (((u1 + u2) * (u0 + u2) * (u0 + u1)) ^ 2 *
          (u2 * (u1 + u2) * (u2 * (u0 + u2)) * (u1 * u0))) := by
    have h := strict_poly u0 u1 u2
    calc 729 * (u0 * u1 * u2) ^ 4
        = (729 * (u0 ^ 3 * u1 ^ 3 * u2 ^ 2)) * (u0 * u1 * u2 ^ 2) := by ring
      _ ≤ (4 * ((u1 + u2) ^ 3 * (u0 + u2) ^ 3 * (u0 + u1) ^ 2)) * (u0 * u1 * u2 ^ 2) :=
          Nat.mul_le_mul_right _ h
      _ = 4 * (((u1 + u2) * (u0 + u2) * (u0 + u1)) ^ 2 *
            (u2 * (u1 + u2) * (u2 * (u0 + u2)) * (u1 * u0))) := by ring
  refine le_trans hstep ?_
  refine Nat.mul_le_mul_left _ (Nat.mul_le_mul ?_ ?_)
  · exact Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.mul_le_mul hd0 hd1) hd2) 2
  · exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul he01 he02) (Nat.mul_le_mul he10 he12))
      (Nat.mul_le_mul he20 he21)

/-! ## Case A: a compatible labelling of the three cells by the middle colours -/

/-- **The labelling of case A.**  If no cell carries two *different* middle colours, the partial
map "cell ↦ its middle colour" is a well-defined injection, and extends (Hall, three sets) to a
bijection `ψ : Fin 3 → Z`.  This is the labelling `ℓ` of UM-095. -/
theorem exists_label (h : IsPathPattern Z a b)
    (hA : ∀ i, a i ∉ Z ∨ b i ∉ Z ∨ a i = b i) :
    ∃ ψ : Fin 3 → ℕ, Function.Injective ψ ∧ (∀ i, ψ i ∈ Z) ∧
      (∀ i, a i ∈ Z → a i = ψ i) ∧ (∀ i, b i ∈ Z → b i = ψ i) := by
  classical
  obtain ⟨e, hev⟩ : ∃ e : Fin 3 → ℕ, ∀ i, e i = if a i ∈ Z then a i else b i :=
    ⟨_, fun _ => rfl⟩
  have hene : ∀ i j : Fin 3, i ≠ j → e i ≠ e j := by
    intro i j hij hee
    rw [hev i, hev j] at hee
    by_cases hai : a i ∈ Z <;> by_cases haj : a j ∈ Z
    · rw [if_pos hai, if_pos haj] at hee; exact hij (h.injA hee)
    · rw [if_pos hai, if_neg haj] at hee; exact hij (h.extEq i j hee)
    · rw [if_neg hai, if_pos haj] at hee; exact hij (h.extEq j i hee.symm).symm
    · rw [if_neg hai, if_neg haj] at hee; exact hij (h.injB hee)
  obtain ⟨T, hTv⟩ : ∃ T : Fin 3 → Finset ℕ, ∀ i, T i = if e i ∈ Z then {e i} else Z :=
    ⟨_, fun _ => rfl⟩
  have hTsub : ∀ i, T i ⊆ Z := by
    intro i
    by_cases hi : e i ∈ Z
    · rw [hTv i, if_pos hi]; simpa using hi
    · rw [hTv i, if_neg hi]
  have h1 : ∀ i, 1 ≤ (T i).card := by
    intro i
    by_cases hi : e i ∈ Z
    · rw [hTv i, if_pos hi]; simp
    · rw [hTv i, if_neg hi, h.cardZ]; omega
  have h2 : ∀ i j : Fin 3, i ≠ j → 2 ≤ (T i ∪ T j).card := by
    intro i j hij
    by_cases hi : e i ∈ Z
    · by_cases hj : e j ∈ Z
      · have hu : T i ∪ T j = {e i, e j} := by
          rw [hTv i, hTv j, if_pos hi, if_pos hj, Finset.singleton_union]
        rw [hu, Finset.card_insert_of_notMem (by simpa using hene i j hij),
          Finset.card_singleton]
      · have hz : Z ⊆ T i ∪ T j := by
          rw [hTv j, if_neg hj]; exact Finset.subset_union_right
        have h4 := Finset.card_le_card hz
        have h5 := h.cardZ
        omega
    · have hz : Z ⊆ T i ∪ T j := by
        rw [hTv i, if_neg hi]; exact Finset.subset_union_left
      have h4 := Finset.card_le_card hz
      have h5 := h.cardZ
      omega
  have h3 : 3 ≤ ((univ : Finset (Fin 3)).biUnion T).card := by
    by_cases hi : ∀ i, e i ∈ Z
    · have e0 : T 0 = {e 0} := by rw [hTv 0, if_pos (hi 0)]
      have e1 : T 1 = {e 1} := by rw [hTv 1, if_pos (hi 1)]
      have e2 : T 2 = {e 2} := by rw [hTv 2, if_pos (hi 2)]
      have hset : (univ : Finset (Fin 3)).biUnion T = {e 0, e 1, e 2} := by
        ext z
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨i, hz⟩
          rw [hTv i, if_pos (hi i), Finset.mem_singleton] at hz
          subst hz
          fin_cases i
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        · rintro (rfl | rfl | rfl)
          · exact ⟨0, by rw [e0]; simp⟩
          · exact ⟨1, by rw [e1]; simp⟩
          · exact ⟨2, by rw [e2]; simp⟩
      rw [hset, Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hene 0 1 (by decide), hene 0 2 (by decide)⟩),
        Finset.card_insert_of_notMem (by simpa using hene 1 2 (by decide)),
        Finset.card_singleton]
    · obtain ⟨i, hii⟩ := not_forall.mp hi
      have hz : Z ⊆ (univ : Finset (Fin 3)).biUnion T := by
        have hTi : T i = Z := by rw [hTv i, if_neg hii]
        exact hTi ▸ Finset.subset_biUnion_of_mem T (Finset.mem_univ i)
      have h4 := Finset.card_le_card hz
      have h5 := h.cardZ
      omega
  obtain ⟨ψ, hψinj, hψmem⟩ := exists_inj_mem3 h1 h2 h3
  have hψZ : ∀ i, ψ i ∈ Z := fun i => hTsub i (hψmem i)
  have hpin : ∀ i, e i ∈ Z → ψ i = e i := by
    intro i hi
    have hm := hψmem i
    rw [hTv i, if_pos hi] at hm
    simpa using hm
  refine ⟨ψ, hψinj, hψZ, ?_, ?_⟩
  · intro i hai
    have he : e i = a i := by rw [hev i, if_pos hai]
    rw [hpin i (by rw [he]; exact hai), he]
  · intro i hbi
    by_cases hai : a i ∈ Z
    · have hab : a i = b i := by
        rcases hA i with hh | hh | hh
        · exact absurd hai hh
        · exact absurd hbi hh
        · exact hh
      have he : e i = b i := by rw [hev i, if_pos hai, hab]
      rw [hpin i (by rw [he]; exact hbi), he]
    · have he : e i = b i := by rw [hev i, if_neg hai]
      rw [hpin i (by rw [he]; exact hbi), he]

/-! ## Case A: the nine cell bounds against the labelling -/

theorem prod_three_perm (f : Fin 3 → ℕ) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : ∏ t : Fin 3, f t = f i * f j * f k := by
  have huniv : ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [hij, hik]),
      Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton, Fintype.card_fin]
  rw [← huniv, Finset.prod_insert (by simp [hij, hik]),
    Finset.prod_insert (by simp [hjk]), Finset.prod_singleton, mul_assoc]

variable {ψ : Fin 3 → ℕ}

theorem label_ne_a (hψinj : Function.Injective ψ) (hψZ : ∀ i, ψ i ∈ Z)
    (hpa : ∀ i, a i ∈ Z → a i = ψ i) {i j : Fin 3} (hij : j ≠ i) : ψ j ≠ a i := by
  intro hh
  by_cases hai : a i ∈ Z
  · exact hij (hψinj (hh.trans (hpa i hai)))
  · exact hai (hh ▸ hψZ j)

theorem label_ne_b (hψinj : Function.Injective ψ) (hψZ : ∀ i, ψ i ∈ Z)
    (hpb : ∀ i, b i ∈ Z → b i = ψ i) {i j : Fin 3} (hij : j ≠ i) : ψ j ≠ b i := by
  intro hh
  by_cases hbi : b i ∈ Z
  · exact hij (hψinj (hh.trans (hpb i hbi)))
  · exact hbi (hh ▸ hψZ j)

theorem label_ne_b_hole (hψZ : ∀ i, ψ i ∈ Z) {i j : Fin 3} (hhole : b i ∉ Z) :
    ψ j ≠ b i := fun hh => hhole (hh ▸ hψZ j)

/-- **The one-hole bound of case A.**  With a labelling `ψ` and a cell `i₂` whose `b`-endpoint
misses the middle list, the nine cells dominate the one-hole pattern, and `strict_assemble`
closes. -/
theorem strict_caseA_hole (h : IsPathPattern Z a b) (x : ℕ → ℕ)
    (hψinj : Function.Injective ψ) (hψZ : ∀ i, ψ i ∈ Z)
    (hpa : ∀ i, a i ∈ Z → a i = ψ i) (hpb : ∀ i, b i ∈ Z → b i = ψ i)
    (i0 i1 i2 : Fin 3) (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2)
    (hhole : b i2 ∉ Z) :
    729 * (∏ z ∈ Z, x z) ^ 4 ≤ 4 *
      ((pathN Z x (a i0) (b i0) * pathN Z x (a i1) (b i1) * pathN Z x (a i2) (b i2)) ^ 2 *
       (pathN Z x (a i0) (b i1) * pathN Z x (a i0) (b i2) *
        (pathN Z x (a i1) (b i0) * pathN Z x (a i1) (b i2)) *
        (pathN Z x (a i2) (b i0) * pathN Z x (a i2) (b i1)))) := by
  classical
  have hXeq : (∏ z ∈ Z, x z) = x (ψ i0) * x (ψ i1) * x (ψ i2) := by
    rw [← enum_image h.cardZ hψZ hψinj, Finset.prod_image (fun p _ q _ hh => hψinj hh)]
    exact prod_three_perm (fun t => x (ψ t)) i0 i1 i2 h01 h02 h12
  have hψne : ∀ p q : Fin 3, p ≠ q → ψ p ≠ ψ q := fun p q hpq hh => hpq (hψinj hh)
  -- single-colour bounds
  have hsingle : ∀ p i j : Fin 3, p ≠ i → p ≠ j → x (ψ p) ≤ pathN Z x (a i) (b j) := by
    intro p i j hpi hpj
    exact single_le_pathN (hψZ p) (label_ne_a hψinj hψZ hpa hpi)
      (label_ne_b hψinj hψZ hpb hpj)
  have hpair : ∀ p q i j : Fin 3, p ≠ q → p ≠ i → p ≠ j → q ≠ i → q ≠ j →
      x (ψ p) + x (ψ q) ≤ pathN Z x (a i) (b j) := by
    intro p q i j hpq hpi hpj hqi hqj
    exact pair_le_pathN (hψZ p) (hψZ q) (hψne p q hpq)
      (label_ne_a hψinj hψZ hpa hpi) (label_ne_b hψinj hψZ hpb hpj)
      (label_ne_a hψinj hψZ hpa hqi) (label_ne_b hψinj hψZ hpb hqj)
  have hpairH : ∀ p q i : Fin 3, p ≠ q → p ≠ i → q ≠ i →
      x (ψ p) + x (ψ q) ≤ pathN Z x (a i) (b i2) := by
    intro p q i hpq hpi hqi
    exact pair_le_pathN (hψZ p) (hψZ q) (hψne p q hpq)
      (label_ne_a hψinj hψZ hpa hpi) (label_ne_b_hole hψZ hhole)
      (label_ne_a hψinj hψZ hpa hqi) (label_ne_b_hole hψZ hhole)
  rw [hXeq]
  refine strict_assemble
    (hpair i1 i2 i0 i0 h12 (Ne.symm h01) (Ne.symm h01) (Ne.symm h02) (Ne.symm h02))
    (hpair i0 i2 i1 i1 h02 h01 h01 (Ne.symm h12) (Ne.symm h12))
    (hpairH i0 i1 i2 h01 h02 h12)
    (hsingle i2 i0 i1 (Ne.symm h02) (Ne.symm h12))
    (hpairH i1 i2 i0 h12 (Ne.symm h01) (Ne.symm h02))
    (hsingle i2 i1 i0 (Ne.symm h12) (Ne.symm h02))
    (hpairH i0 i2 i1 h02 h01 (Ne.symm h12))
    (hsingle i1 i2 i0 h12 (Ne.symm h01))
    (hsingle i0 i2 i1 h02 h01)

/-! ## Case A assembled -/

theorem pathDiag_swap (Z : Finset ℕ) (x : ℕ → ℕ) (a b : Fin 3 → ℕ) :
    pathDiag Z x b a = pathDiag Z x a b :=
  Finset.prod_congr rfl fun i _ => pathN_symm Z x (b i) (a i)

theorem pathOff_swap (Z : Finset ℕ) (x : ℕ → ℕ) (a b : Fin 3 → ℕ) :
    pathOff Z x b a = pathOff Z x a b := by
  rw [pathOff_eq, pathOff_eq, pathN_symm Z x (b 0) (a 1), pathN_symm Z x (b 0) (a 2),
    pathN_symm Z x (b 1) (a 0), pathN_symm Z x (b 1) (a 2), pathN_symm Z x (b 2) (a 0),
    pathN_symm Z x (b 2) (a 1)]
  ring

/-- Case A with the hole on the `b` side, at any of the three cells. -/
theorem strict_caseA_of_bhole (h : IsPathPattern Z a b) (x : ℕ → ℕ)
    (hpsinj : Function.Injective ψ) (hψZ : ∀ i, ψ i ∈ Z)
    (hpa : ∀ i, a i ∈ Z → a i = ψ i) (hpb : ∀ i, b i ∈ Z → b i = ψ i)
    (i2 : Fin 3) (hi2 : b i2 ∉ Z) :
    729 * (∏ z ∈ Z, x z) ^ 4 ≤ 4 * (pathDiag Z x a b ^ 2 * pathOff Z x a b) := by
  rw [pathDiag_eq, pathOff_eq]
  have hcases : i2 = 0 ∨ i2 = 1 ∨ i2 = 2 := by fin_cases i2 <;> simp
  rcases hcases with rfl | rfl | rfl
  · exact le_trans (strict_caseA_hole h x hpsinj hψZ hpa hpb 1 2 0
      (by decide) (by decide) (by decide) hi2) (le_of_eq (by ring))
  · exact le_trans (strict_caseA_hole h x hpsinj hψZ hpa hpb 2 0 1
      (by decide) (by decide) (by decide) hi2) (le_of_eq (by ring))
  · exact le_trans (strict_caseA_hole h x hpsinj hψZ hpa hpb 0 1 2
      (by decide) (by decide) (by decide) hi2) (le_of_eq (by ring))

/-- **Case A of the strict cone point.**  No cell carries two different middle colours; then the
labelling exists, and `a ≠ b` forces a cell with an endpoint outside the middle list. -/
theorem strict_caseA (h : IsPathPattern Z a b) (x : ℕ → ℕ)
    (hA : ∀ i, a i ∉ Z ∨ b i ∉ Z ∨ a i = b i) (hne : a ≠ b) :
    729 * (∏ z ∈ Z, x z) ^ 4 ≤ 4 * (pathDiag Z x a b ^ 2 * pathOff Z x a b) := by
  classical
  obtain ⟨ψ, hψinj, hψZ, hpa, hpb⟩ := exists_label h hA
  by_cases hb : ∃ i, b i ∉ Z
  · obtain ⟨i2, hi2⟩ := hb
    exact strict_caseA_of_bhole h x hψinj hψZ hpa hpb i2 hi2
  · push_neg at hb
    by_cases ha : ∃ i, a i ∉ Z
    · obtain ⟨i2, hi2⟩ := ha
      have hswap : IsPathPattern Z b a :=
        ⟨h.cardZ, h.injB, h.injA, fun i j hij => (h.extEq j i hij.symm).symm⟩
      have hkey := strict_caseA_of_bhole (a := b) (b := a) (ψ := ψ) hswap x hψinj hψZ hpb hpa
        i2 hi2
      rwa [pathDiag_swap, pathOff_swap] at hkey
    · push_neg at ha
      exact absurd (funext fun i => (hpa i (ha i)).trans (hpb i (hb i)).symm) hne

/-! ## Case B: one cell carries two different middle colours -/

theorem caseB_poly1 (A B C : ℕ) :
    729 * (A * B * C) ^ 4
      ≤ 4 * ((C * (A + B) * (A + B)) ^ 2 *
          ((B + C) * (B + C) * (A * (A + C) * ((A + B) * (A + B))))) := by
  have h1 : 64 * (A ^ 3 * B ^ 3) ≤ (A + B) ^ 6 := by
    have h := amgm_two A B
    calc 64 * (A ^ 3 * B ^ 3) = (2 ^ 2 * (A * B)) ^ 3 := by ring
      _ ≤ ((A + B) ^ 2) ^ 3 := Nat.pow_le_pow_left h 3
      _ = (A + B) ^ 6 := by ring
  have h2 : 4 * (B * C) ≤ (B + C) ^ 2 := by
    have h := amgm_two B C; simpa using h
  have h3 : C ≤ A + C := Nat.le_add_left _ _
  calc 729 * (A * B * C) ^ 4 ≤ 1024 * (A * B * C) ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
    _ = 4 * ((C * C) * ((64 * (A ^ 3 * B ^ 3)) * ((4 * (B * C)) * (A * C)))) := by ring
    _ ≤ 4 * ((C * C) * ((A + B) ^ 6 * ((B + C) ^ 2 * (A * (A + C))))) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (Nat.mul_le_mul_left _ h3))))
    _ = 4 * ((C * (A + B) * (A + B)) ^ 2 *
          ((B + C) * (B + C) * (A * (A + C) * ((A + B) * (A + B))))) := by ring

theorem caseB_poly2 (A B C : ℕ) :
    729 * (A * B * C) ^ 4
      ≤ 4 * ((C * (A + B) * (A + B)) ^ 2 *
          (B * (B + C) * ((A + C) * (A + C) * ((A + B) * (A + B))))) := by
  have h1 : 64 * (A ^ 3 * B ^ 3) ≤ (A + B) ^ 6 := by
    have h := amgm_two A B
    calc 64 * (A ^ 3 * B ^ 3) = (2 ^ 2 * (A * B)) ^ 3 := by ring
      _ ≤ ((A + B) ^ 2) ^ 3 := Nat.pow_le_pow_left h 3
      _ = (A + B) ^ 6 := by ring
  have h2 : 4 * (A * C) ≤ (A + C) ^ 2 := by
    have h := amgm_two A C; simpa using h
  have h3 : C ≤ B + C := Nat.le_add_left _ _
  calc 729 * (A * B * C) ^ 4 ≤ 1024 * (A * B * C) ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
    _ = 4 * ((C * C) * ((64 * (A ^ 3 * B ^ 3)) * (B * ((4 * (A * C)) * C)))) := by ring
    _ ≤ 4 * ((C * C) * ((A + B) ^ 6 * (B * ((A + C) ^ 2 * (B + C))))) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h3))))
    _ = 4 * ((C * (A + B) * (A + B)) ^ 2 *
          (B * (B + C) * ((A + C) * (A + C) * ((A + B) * (A + B))))) := by ring

theorem caseB_poly3 (A B C : ℕ) :
    729 * (A * B * C) ^ 4
      ≤ 4 * ((C * ((A + B) * (A + B + C))) ^ 2 *
          (B * (B + C) * (A * (A + C) * ((A + B) * (A + B))))) := by
  have h1 : 16 * (A ^ 2 * B ^ 2) ≤ (A + B) ^ 4 := by
    have h := amgm_two A B
    calc 16 * (A ^ 2 * B ^ 2) = (2 ^ 2 * (A * B)) ^ 2 := by ring
      _ ≤ ((A + B) ^ 2) ^ 2 := Nat.pow_le_pow_left h 2
      _ = (A + B) ^ 4 := by ring
  have h2 : (A + C) * (B + C) ≤ (A + B + C) ^ 2 := by nlinarith [Nat.zero_le A, Nat.zero_le B]
  have h3 : 4 * (A * C) ≤ (A + C) ^ 2 := by have h := amgm_two A C; simpa using h
  have h4 : 4 * (B * C) ≤ (B + C) ^ 2 := by have h := amgm_two B C; simpa using h
  have hsq : 16 * (A * B * C ^ 2) ≤ ((A + C) * (B + C)) ^ 2 := by
    calc 16 * (A * B * C ^ 2) = (4 * (A * C)) * (4 * (B * C)) := by ring
      _ ≤ (A + C) ^ 2 * (B + C) ^ 2 := Nat.mul_le_mul h3 h4
      _ = ((A + C) * (B + C)) ^ 2 := by ring
  calc 729 * (A * B * C) ^ 4 ≤ 1024 * (A * B * C) ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
    _ = 4 * ((C * C) * ((16 * (A ^ 2 * B ^ 2)) * (A * B * (16 * (A * B * C ^ 2))))) := by ring
    _ ≤ 4 * ((C * C) * ((A + B) ^ 4 * (A * B * ((A + C) * (B + C)) ^ 2))) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul h1 (Nat.mul_le_mul_left _ hsq)))
    _ = 4 * ((C * C) * ((A + B) ^ 4 * (A * B * (((A + C) * (B + C)) * ((A + C) * (B + C)))))) := by
        ring
    _ ≤ 4 * ((C * C) * ((A + B) ^ 4 * (A * B * (((A + B + C) ^ 2) * ((A + C) * (B + C)))))) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2))))
    _ = 4 * ((C * ((A + B) * (A + B + C))) ^ 2 *
          (B * (B + C) * (A * (A + C) * ((A + B) * (A + B))))) := by ring

/-- **Case B of the strict cone point**, at an explicit cell triple `(i,p,q)`: the cell `i`
carries two different middle colours `a i ≠ b i`, and `c` is the third. -/
theorem strict_caseB_core (h : IsPathPattern Z a b) (x : ℕ → ℕ)
    (i p q : Fin 3) (hip : i ≠ p) (hiq : i ≠ q) (hpq : p ≠ q)
    (hai : a i ∈ Z) (hbi : b i ∈ Z) (hnei : a i ≠ b i) :
    729 * (∏ z ∈ Z, x z) ^ 4 ≤ 4 *
      ((pathN Z x (a i) (b i) * pathN Z x (a p) (b p) * pathN Z x (a q) (b q)) ^ 2 *
       (pathN Z x (a i) (b p) * pathN Z x (a i) (b q) *
        (pathN Z x (a p) (b i) * pathN Z x (a p) (b q)) *
        (pathN Z x (a q) (b i) * pathN Z x (a q) (b p)))) := by
  classical
  obtain ⟨c, hcZ, hca, hcb, hZeq, -⟩ := exists_third h hai hbi hnei
  set A := x (a i) with hA
  set B := x (b i) with hB
  set C := x c with hC
  have hXeq : (∏ z ∈ Z, x z) = A * B * C := by
    rw [hZeq, Finset.prod_insert (by simp [hnei, Ne.symm hca]),
      Finset.prod_insert (by simp [Ne.symm hcb]), Finset.prod_singleton]
    rw [hA, hB, hC]; ring
  -- separation facts
  have haa : ∀ j : Fin 3, j ≠ i → a i ≠ a j := fun j hj hh => hj (h.injA hh).symm
  have hbb : ∀ j : Fin 3, j ≠ i → b i ≠ b j := fun j hj hh => hj (h.injB hh).symm
  have hab : ∀ j : Fin 3, j ≠ i → a i ≠ b j := fun j hj hh => hj (h.extEq i j hh).symm
  have hba : ∀ j : Fin 3, j ≠ i → b i ≠ a j := fun j hj hh => hj (h.extEq j i hh.symm)
  -- the diagonal at `i`
  have hdi : C ≤ pathN Z x (a i) (b i) := single_le_pathN hcZ hca hcb
  -- every cell away from row `i` and column `i` clears `A + B`
  have hfour : ∀ r s : Fin 3, r ≠ i → s ≠ i → A + B ≤ pathN Z x (a r) (b s) := by
    intro r s hr hs
    exact pair_le_pathN hai hbi hnei (haa r hr) (hab s hs) (hba r hr) (hbb s hs)
  -- row `i`
  have hrow : ∀ s : Fin 3, s ≠ i → B ≤ pathN Z x (a i) (b s) := fun s hs =>
    single_le_pathN hbi (Ne.symm hnei) (hbb s hs)
  have hrowS : ∀ s : Fin 3, s ≠ i → b s ≠ c → B + C ≤ pathN Z x (a i) (b s) := by
    intro s hs hbs
    exact pair_le_pathN hbi hcZ (Ne.symm hcb) (Ne.symm hnei) (hbb s hs) hca (Ne.symm hbs)
  -- column `i`
  have hcol : ∀ r : Fin 3, r ≠ i → A ≤ pathN Z x (a r) (b i) := fun r hr =>
    single_le_pathN hai (haa r hr) hnei
  have hcolS : ∀ r : Fin 3, r ≠ i → a r ≠ c → A + C ≤ pathN Z x (a r) (b i) := by
    intro r hr har
    exact pair_le_pathN hai hcZ (Ne.symm hca) (haa r hr) hnei (Ne.symm har) hcb
  -- a clean diagonal cell clears `A + B + C`
  have hfull : ∀ r : Fin 3, r ≠ i → a r ≠ c → b r ≠ c →
      A + B + C ≤ pathN Z x (a r) (b r) := by
    intro r hr har hbr
    exact triple_le_pathN hai hbi hcZ hnei (Ne.symm hca) (Ne.symm hcb)
      (haa r hr) (hab r hr) (hba r hr) (hbb r hr) (Ne.symm har) (Ne.symm hbr)
  -- the always-available row and column products
  have hrow2 : B * (B + C) ≤ pathN Z x (a i) (b p) * pathN Z x (a i) (b q) := by
    by_cases hbp : b p = c
    · have hbq : b q ≠ c := fun hh => hpq (h.injB (hbp.trans hh.symm))
      exact Nat.mul_le_mul (hrow p (Ne.symm hip)) (hrowS q (Ne.symm hiq) hbq)
    · calc B * (B + C) = (B + C) * B := by ring
        _ ≤ _ := Nat.mul_le_mul (hrowS p (Ne.symm hip) hbp) (hrow q (Ne.symm hiq))
  have hcol2 : A * (A + C) ≤ pathN Z x (a p) (b i) * pathN Z x (a q) (b i) := by
    by_cases hap : a p = c
    · have haq : a q ≠ c := fun hh => hpq (h.injA (hap.trans hh.symm))
      exact Nat.mul_le_mul (hcol p (Ne.symm hip)) (hcolS q (Ne.symm hiq) haq)
    · calc A * (A + C) = (A + C) * A := by ring
        _ ≤ _ := Nat.mul_le_mul (hcolS p (Ne.symm hip) hap) (hcol q (Ne.symm hiq))
  have hoff : (A + B) * (A + B) ≤ pathN Z x (a p) (b q) * pathN Z x (a q) (b p) :=
    Nat.mul_le_mul (hfour p q (Ne.symm hip) (Ne.symm hiq)) (hfour q p (Ne.symm hiq) (Ne.symm hip))
  rw [hXeq]
  by_cases hB1 : b p ≠ c ∧ b q ≠ c
  · -- both cells of row `i` are strict
    have hrowS2 : (B + C) * (B + C) ≤ pathN Z x (a i) (b p) * pathN Z x (a i) (b q) :=
      Nat.mul_le_mul (hrowS p (Ne.symm hip) hB1.1) (hrowS q (Ne.symm hiq) hB1.2)
    have hD : C * (A + B) * (A + B)
        ≤ pathN Z x (a i) (b i) * pathN Z x (a p) (b p) * pathN Z x (a q) (b q) :=
      Nat.mul_le_mul (Nat.mul_le_mul hdi (hfour p p (Ne.symm hip) (Ne.symm hip)))
        (hfour q q (Ne.symm hiq) (Ne.symm hiq))
    refine le_trans (caseB_poly1 A B C) ?_
    refine Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hD 2) ?_)
    calc (B + C) * (B + C) * (A * (A + C) * ((A + B) * (A + B)))
        ≤ (pathN Z x (a i) (b p) * pathN Z x (a i) (b q)) *
            ((pathN Z x (a p) (b i) * pathN Z x (a q) (b i)) *
              (pathN Z x (a p) (b q) * pathN Z x (a q) (b p))) :=
          Nat.mul_le_mul hrowS2 (Nat.mul_le_mul hcol2 hoff)
      _ = _ := by ring
  · by_cases hB2 : a p ≠ c ∧ a q ≠ c
    · have hcolS2 : (A + C) * (A + C) ≤ pathN Z x (a p) (b i) * pathN Z x (a q) (b i) :=
        Nat.mul_le_mul (hcolS p (Ne.symm hip) hB2.1) (hcolS q (Ne.symm hiq) hB2.2)
      have hD : C * (A + B) * (A + B)
          ≤ pathN Z x (a i) (b i) * pathN Z x (a p) (b p) * pathN Z x (a q) (b q) :=
        Nat.mul_le_mul (Nat.mul_le_mul hdi (hfour p p (Ne.symm hip) (Ne.symm hip)))
          (hfour q q (Ne.symm hiq) (Ne.symm hiq))
      refine le_trans (caseB_poly2 A B C) ?_
      refine Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hD 2) ?_)
      calc B * (B + C) * ((A + C) * (A + C) * ((A + B) * (A + B)))
          ≤ (pathN Z x (a i) (b p) * pathN Z x (a i) (b q)) *
              ((pathN Z x (a p) (b i) * pathN Z x (a q) (b i)) *
                (pathN Z x (a p) (b q) * pathN Z x (a q) (b p))) :=
            Nat.mul_le_mul hrow2 (Nat.mul_le_mul hcolS2 hoff)
        _ = _ := by ring
    · -- a cell `r ≠ i` carries `c` on both sides; the remaining diagonal cell is full
      have hbex : ∃ r : Fin 3, r ≠ i ∧ b r = c := by
        rcases not_and_or.mp hB1 with hh | hh
        · exact ⟨p, Ne.symm hip, not_not.mp hh⟩
        · exact ⟨q, Ne.symm hiq, not_not.mp hh⟩
      have haex : ∃ r : Fin 3, r ≠ i ∧ a r = c := by
        rcases not_and_or.mp hB2 with hh | hh
        · exact ⟨p, Ne.symm hip, not_not.mp hh⟩
        · exact ⟨q, Ne.symm hiq, not_not.mp hh⟩
      obtain ⟨rb, hrbi, hrb⟩ := hbex
      obtain ⟨ra, hrai, hra⟩ := haex
      have hrab : ra = rb := h.extEq ra rb (by rw [hra, hrb])
      subst hrab
      -- the third cell
      have hother : ∀ t : Fin 3, t ≠ i → t ≠ ra → a t ≠ c ∧ b t ≠ c := by
        intro t hti htr
        exact ⟨fun hh => htr (h.injA (hh.trans hra.symm)),
          fun hh => htr (h.injB (hh.trans hrb.symm))⟩
      have hD : C * ((A + B) * (A + B + C))
          ≤ pathN Z x (a i) (b i) * pathN Z x (a p) (b p) * pathN Z x (a q) (b q) := by
        have hcase : ra = p ∨ ra = q := by
          have huniv : ({i, p, q} : Finset (Fin 3)) = Finset.univ := by
            apply Finset.eq_univ_of_card
            rw [Finset.card_insert_of_notMem (by simp [hip, hiq]),
              Finset.card_insert_of_notMem (by simp [hpq]), Finset.card_singleton,
              Fintype.card_fin]
          have hmem : ra ∈ ({i, p, q} : Finset (Fin 3)) := by
            rw [huniv]; exact Finset.mem_univ _
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with hh | hh | hh
          · exact absurd hh hrai
          · exact Or.inl hh
          · exact Or.inr hh
        rcases hcase with rfl | rfl
        · obtain ⟨hqa, hqb⟩ := hother q (Ne.symm hiq) (Ne.symm hpq)
          calc C * ((A + B) * (A + B + C)) = C * (A + B) * (A + B + C) := by ring
            _ ≤ _ := Nat.mul_le_mul
                (Nat.mul_le_mul hdi (hfour ra ra (Ne.symm hip) (Ne.symm hip)))
                (hfull q (Ne.symm hiq) hqa hqb)
        · obtain ⟨hpa, hpb⟩ := hother p (Ne.symm hip) hpq
          calc C * ((A + B) * (A + B + C)) = C * (A + B + C) * (A + B) := by ring
            _ ≤ _ := Nat.mul_le_mul
                (Nat.mul_le_mul hdi (hfull p (Ne.symm hip) hpa hpb))
                (hfour ra ra (Ne.symm hiq) (Ne.symm hiq))
      refine le_trans (caseB_poly3 A B C) ?_
      refine Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hD 2) ?_)
      calc B * (B + C) * (A * (A + C) * ((A + B) * (A + B)))
          ≤ (pathN Z x (a i) (b p) * pathN Z x (a i) (b q)) *
              ((pathN Z x (a p) (b i) * pathN Z x (a q) (b i)) *
                (pathN Z x (a p) (b q) * pathN Z x (a q) (b p))) :=
            Nat.mul_le_mul hrow2 (Nat.mul_le_mul hcol2 hoff)
        _ = _ := by ring

/-! ## The strict cone point -/

/-- **The strict `(2,1)` cone point at `k = 3`** (UM-095 in the form `path_strict_pow` consumes
it): if the two terminal enumerations differ — equivalently, if the two terminal lists are
different sets — then the `(2,1)` cone point improves from `2^6 = 64` to `729/4 = 182.25`.

Sharp: equality at `Z = {0,1,2}`, `a = (0,1,2)`, `b = (0,1,∗)` with weights `(2,2,1)`.

This discharges the hypothesis `h3` of `path_strict_pow`, whose strict factor
`(729/256)^n` per `(2,1)` block is the resource the non-identity holonomy branch of
`cycle_gm_bound_even` spends. -/
theorem path_cone_two_one_strict (h : IsPathPattern Z a b) (x : ℕ → ℕ) (hne : a ≠ b) :
    729 * (∏ z ∈ Z, x z) ^ 4 ≤ 4 * (pathDiag Z x a b ^ 2 * pathOff Z x a b) := by
  classical
  by_cases hB : ∃ i, a i ∈ Z ∧ b i ∈ Z ∧ a i ≠ b i
  · obtain ⟨i, hai, hbi, hnei⟩ := hB
    rw [pathDiag_eq, pathOff_eq]
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hcases with rfl | rfl | rfl
    · exact le_trans (strict_caseB_core h x 0 1 2 (by decide) (by decide) (by decide)
        hai hbi hnei) (le_of_eq (by ring))
    · exact le_trans (strict_caseB_core h x 1 0 2 (by decide) (by decide) (by decide)
        hai hbi hnei) (le_of_eq (by ring))
    · exact le_trans (strict_caseB_core h x 2 0 1 (by decide) (by decide) (by decide)
        hai hbi hnei) (le_of_eq (by ring))
  · refine strict_caseA h x (fun i => ?_) hne
    by_cases h1 : a i ∈ Z
    · by_cases h2 : b i ∈ Z
      · exact Or.inr (Or.inr (by by_contra hh; exact hB ⟨i, h1, h2, hh⟩))
      · exact Or.inr (Or.inl h2)
    · exact Or.inl h1

/-- The strict cone point, packaged for `path_strict_pow`: on an unequal-list two-edge path the
`(M,S) = (2n, n+s)` cone point gains the factor `(729/256)^n` over `path_cone_pow`. -/
theorem path_strict_cone (h : IsPathPattern Z a b) (x : ℕ → ℕ) (hne : a ≠ b) (n s : ℕ) :
    729 ^ n * (∏ z ∈ Z, x z) ^ (4 * n + 2 * s)
      ≤ 4 ^ n * ((pathDiag Z x a b ^ 2 * pathOff Z x a b) ^ n * pathOff Z x a b ^ s) :=
  path_strict_pow (path_cone_two_one_strict h x hne) (path_ray_off h) n s

end Strict

/-! ## Where the hypothesis `a ≠ b` comes from on an even cycle

`exists_terminal_closing_model` produces an enumeration chain `σ` of the terminal lists together
with a closing permutation `P`.  If every internal vertex saw *equal* terminal enumerations, the
chain would be constant and `P` would be the identity.  So a nontrivial holonomy always exposes
one internal vertex whose two terminal enumerations differ — exactly the input of
`path_cone_two_one_strict`. -/

section Holonomy

/-- A trivial pattern at every internal vertex forces a trivial holonomy. -/
theorem holonomy_one_of_chain_const {M : ℕ} (σ : Fin (M + 1) → Fin 3 → ℕ)
    (P : Equiv.Perm (Fin 3)) (hinj : Function.Injective (σ 0))
    (hord : ∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1), σ ⟨i.val + 1, h⟩ = σ i)
    (hcl : (fun q => σ 0 (P q)) = σ (Fin.last M)) : P = 1 := by
  have hall : ∀ k : ℕ, ∀ hk : k < M + 1, σ ⟨k, hk⟩ = σ 0 := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hk' : k < M + 1 := by omega
      have hstep := hord ⟨k, hk'⟩ (by simpa using hk)
      calc σ ⟨k + 1, hk⟩ = σ ⟨(⟨k, hk'⟩ : Fin (M + 1)).val + 1, by simpa using hk⟩ := rfl
        _ = σ ⟨k, hk'⟩ := hstep
        _ = σ 0 := ih hk'
  have hlast : σ (Fin.last M) = σ 0 := hall M (by omega)
  rw [hlast] at hcl
  refine Equiv.ext fun q => ?_
  have hq : σ 0 (P q) = σ 0 q := congrFun hcl q
  simpa using hinj hq

/-- **A nontrivial holonomy exposes an unequal internal vertex.** -/
theorem exists_unequal_pattern {M : ℕ} (σ : Fin (M + 1) → Fin 3 → ℕ) (P : Equiv.Perm (Fin 3))
    (hinj : Function.Injective (σ 0)) (hP : P ≠ 1) :
    (∃ (i : Fin (M + 1)) (h : i.val + 1 < M + 1), σ ⟨i.val + 1, h⟩ ≠ σ i) ∨
      (fun q => σ 0 (P q)) ≠ σ (Fin.last M) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact hP (holonomy_one_of_chain_const σ P hinj (fun i h => h1 i h) h2)

end Holonomy

end ListColoring


/-! # The identity-holonomy branch of `cycle_gm_bound_even` (all even cycles)

Reproduced from the verified development, on top of `Cacti.EvenBase` (so that its own copy of
`path_cone_four_one` is dropped in favour of the repository's).
-/

namespace ListColoring

open Finset

variable {Z : Finset ℕ} {x : ℕ → ℕ} {a b : Fin 3 → ℕ}


/-- Identity holonomy, every edge: `(2T+2, T) = (4,1) + (T-1)·(2,1)`. -/
theorem path_identity_vertex (h : IsPathPattern Z a b) (T : ℕ) (hT : 1 ≤ T) :
    2 ^ (6 * T + 6) * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      ≤ pathDiag Z x a b ^ (2 * T + 2) * pathOff Z x a b ^ T := by
  have h41 := path_cone_four_one (x := x) h
  have h21 := path_cone_two_one (x := x) h
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  have hpow : (2 ^ 6 * (∏ z ∈ Z, x z) ^ 4) ^ t
      ≤ (pathDiag Z x a b ^ 2 * pathOff Z x a b) ^ t := Nat.pow_le_pow_left h21 t
  calc 2 ^ (6 * (t + 1) + 6) * (∏ z ∈ Z, x z) ^ (4 * (t + 1) + 2)
      = (2 ^ 12 * (∏ z ∈ Z, x z) ^ 6) * (2 ^ 6 * (∏ z ∈ Z, x z) ^ 4) ^ t := by
        rw [mul_pow, ← pow_mul, ← pow_mul]; ring
    _ ≤ (pathDiag Z x a b ^ 4 * pathOff Z x a b) *
          (pathDiag Z x a b ^ 2 * pathOff Z x a b) ^ t := Nat.mul_le_mul h41 hpow
    _ = pathDiag Z x a b ^ (2 * (t + 1) + 2) * pathOff Z x a b ^ (t + 1) := by
        rw [mul_pow, ← pow_mul]; ring

end ListColoring


namespace ListColoring

open Finset SimpleGraph RefTensor

/-! ## S0.  The root normalizer of an even cycle is `E = 4 γ_M + 2`. -/

theorem uniformA_three_even (M : ℕ) : uniformA 3 (2 * M + 2) = 4 * gammaPlus M + 2 := by
  have hsum := alpha_add_beta (show 2 ≤ 3 by omega) (2 * M + 1)
  have halt := (beta_alternation (show 2 ≤ 3 by omega) (2 * M + 1)).1 ⟨M, by omega⟩
  have hgam := three_mul_gammaPlus_add_one M
  have hpow : (2 : ℕ) ^ (2 * M + 1) = 2 * 4 ^ M := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [uniformA]
  simp only [show (3 : ℕ) - 1 = 2 from rfl, show 2 * M + 2 - 1 = 2 * M + 1 from rfl] at *
  omega

section Model

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## S1.  The terminal closing model. -/

/-- The terminal chain plus a *global* closing permutation: transplanting `exists_cover_model`
to the terminal cycle and upgrading its `dom`-local clause to a statement about all pairs. -/
theorem exists_terminal_closing_model {M : ℕ} (jx : CycIx M ≃ V) (L : ListAssignment V)
    (hL : IsNListAssignment L 3) :
    ∃ (σ : Fin (M + 1) → Fin 3 → ℕ) (P : Equiv.Perm (Fin 3)),
      (∀ i x, σ i x ∈ L (tv jx i)) ∧ (∀ i, Function.Injective (σ i)) ∧
      (∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1) (x : Fin 3),
          σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x) ∧
      (∀ x y : Fin 3, σ (Fin.last M) x = σ 0 y → y = P x) := by
  classical
  obtain ⟨σ, P, dom, hmem, hinj, hchain, hdom, hclose⟩ :=
    exists_cover_model (V := Fin (M + 1)) (Equiv.refl (Fin (M + 1)))
      (fun i => L (tv jx i)) (fun i => hL (tv jx i))
  refine ⟨σ, P, hmem, hinj, hchain, ?_⟩
  intro x y hxy
  have hy : y ∈ dom := (hdom y).mpr (by rw [← hxy]; exact hmem (Fin.last M) x)
  have h1 : σ (Fin.last M) (P.symm y) = σ 0 y := hclose y hy
  have h2 : P.symm y = x := hinj (Fin.last M) (h1.trans hxy.symm)
  rw [← h2, Equiv.apply_symm_apply]

/-- At `M = 1` the holonomy is forced to be trivial: there is only one terminal pair and the
chain's own bijection already closes it.  Hence `C_4` lands in the identity branch. -/
theorem terminal_closing_model_trivial {M : ℕ} (hM : M = 1) (jx : CycIx M ≃ V)
    (L : ListAssignment V)
    (σ : Fin (M + 1) → Fin 3 → ℕ) (hmem : ∀ i x, σ i x ∈ L (tv jx i))
    (hinj : ∀ i, Function.Injective (σ i))
    (hchain : ∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1) (x : Fin 3),
        σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x) :
    ∀ x y : Fin 3, σ (Fin.last M) x = σ 0 y → y = (1 : Equiv.Perm (Fin 3)) x := by
  subst hM
  intro x y hxy
  have h0 : (0 : Fin 2).val + 1 < 2 := by decide
  have hlast : (⟨(0 : Fin 2).val + 1, h0⟩ : Fin 2) = Fin.last 1 := rfl
  have hy : σ 0 y ∈ L (tv jx ⟨(0 : Fin 2).val + 1, h0⟩) := by
    rw [← hxy, hlast]; exact hmem (Fin.last 1) x
  have h1 := hchain 0 h0 y hy
  rw [hlast] at h1
  have h2 : σ (Fin.last 1) y = σ (Fin.last 1) x := by rw [h1, ← hxy]
  have := hinj (Fin.last 1) h2
  simpa using this

/-! ## S2.  The two path patterns. -/

theorem isPathPattern_ordinary {M : ℕ} (jx : CycIx M ≃ V) (L : ListAssignment V)
    (hL : IsNListAssignment L 3) (σ : Fin (M + 1) → Fin 3 → ℕ)
    (hmem : ∀ i x, σ i x ∈ L (tv jx i)) (hinj : ∀ i, Function.Injective (σ i))
    (hchain : ∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1) (x : Fin 3),
        σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x)
    (i : Fin (M + 1)) (hi : i.val + 1 < M + 1) :
    IsPathPattern (L (iv jx i)) (σ i) (σ (i + 1)) := by
  have hsucc : i + 1 = (⟨i.val + 1, hi⟩ : Fin (M + 1)) := by
    apply Fin.ext
    rw [Fin.val_add_one_of_lt (by exact Fin.lt_def.mpr (by simpa using by omega))]
  refine ⟨hL _, hinj i, hinj (i + 1), ?_⟩
  intro p q hpq
  have hq : σ i p ∈ L (tv jx ⟨i.val + 1, hi⟩) := by
    rw [hpq, ← hsucc]; exact hmem (i + 1) q
  have h1 := hchain i hi p hq
  rw [← hsucc] at h1
  exact hinj (i + 1) (h1.trans hpq)

theorem isPathPattern_closing {M : ℕ} (jx : CycIx M ≃ V) (L : ListAssignment V)
    (hL : IsNListAssignment L 3) (σ : Fin (M + 1) → Fin 3 → ℕ) (P : Equiv.Perm (Fin 3))
    (hinj : ∀ i, Function.Injective (σ i))
    (hclose : ∀ x y : Fin 3, σ (Fin.last M) x = σ 0 y → y = P x) :
    IsPathPattern (L (iv jx (Fin.last M))) (σ (Fin.last M)) (fun q => σ 0 (P q)) := by
  refine ⟨hL _, hinj (Fin.last M), fun p q hpq => P.injective (hinj 0 hpq), ?_⟩
  intro p q hpq
  have := hclose p (P q) hpq
  exact (P.injective this).symm

end Model

end ListColoring


namespace ListColoring
namespace RefTensor

open Finset Matrix

/-- **The two-point pinned path sum.**  With the word forced to take the values `c, d` at the
two ends of the ordinary edge `p`, the transfer product splits at that edge into
`(J+I)^p`, the single entry `(J+I) c d`, and `(J+I)^{N-1-p}`.  This is the exact analogue of
`sum_pathWeight_pin` with two adjacent pinned coordinates. -/
theorem sum_pathWeight_pin_two :
    ∀ (N : ℕ) (e : Fin N) (c d : Fin 3) (g : Fin 3 → Fin 3 → ℕ),
      ∑ a : Fin (N + 1) → Fin 3,
          pathWeight a *
            (if a e.castSucc = c then
                (if a e.succ = d then g (a 0) (a (Fin.last N)) else 0)
              else 0)
        = ∑ i : Fin 3, ∑ j : Fin 3,
            (onesPlus ^ (e : ℕ)) i c *
              (onesPlus c d * ((onesPlus ^ (N - 1 - (e : ℕ))) d j * g i j)) := by
  intro N
  induction N with
  | zero => intro e; exact e.elim0
  | succ N ih =>
    intro e c d g
    refine Fin.cases ?_ ?_ e
    · -- the pinned edge is the first one
      rw [← Equiv.sum_comp (consEq N)
        (fun a => pathWeight a *
          (if a (0 : Fin (N + 1)).castSucc = c then
              (if a (0 : Fin (N + 1)).succ = d then g (a 0) (a (Fin.last (N + 1))) else 0)
            else 0))]
      rw [Fintype.sum_prod_type]
      have hsimp : ∀ (c₀ : Fin 3) (b : Fin (N + 1) → Fin 3),
          pathWeight (consEq N (c₀, b)) *
            (if consEq N (c₀, b) (0 : Fin (N + 1)).castSucc = c then
                (if consEq N (c₀, b) (0 : Fin (N + 1)).succ = d then
                    g (consEq N (c₀, b) 0) (consEq N (c₀, b) (Fin.last (N + 1)))
                  else 0)
              else 0)
            = (if c₀ = c then 1 else 0) *
                (onesPlus c₀ (b 0) *
                  (pathWeight b * (if b 0 = d then g c₀ (b (Fin.last N)) else 0))) := by
        intro c₀ b
        rw [consEq_apply, pathWeight_cons, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
          ← Fin.succ_last, Fin.cons_succ]
        split_ifs <;> ring
      have step : ∀ c₀ : Fin 3,
          (∑ b : Fin (N + 1) → Fin 3,
              pathWeight (consEq N (c₀, b)) *
                (if consEq N (c₀, b) (0 : Fin (N + 1)).castSucc = c then
                    (if consEq N (c₀, b) (0 : Fin (N + 1)).succ = d then
                        g (consEq N (c₀, b) 0) (consEq N (c₀, b) (Fin.last (N + 1)))
                      else 0)
                  else 0))
            = (if c₀ = c then 1 else 0) *
                (onesPlus c₀ d * ∑ j : Fin 3, (onesPlus ^ N) d j * g c₀ j) := by
        intro c₀
        rw [Finset.sum_congr rfl (fun b _ => hsimp c₀ b), ← Finset.mul_sum]
        congr 1
        have hpull : ∀ b : Fin (N + 1) → Fin 3,
            onesPlus c₀ (b 0) *
                (pathWeight b * (if b 0 = d then g c₀ (b (Fin.last N)) else 0))
              = onesPlus c₀ d *
                (pathWeight b * (if b 0 = d then g c₀ (b (Fin.last N)) else 0)) := by
          intro b
          by_cases hb : b 0 = d
          · rw [hb]
          · simp [hb]
        rw [Finset.sum_congr rfl (fun b _ => hpull b), ← Finset.mul_sum]
        congr 1
        have := sum_pathWeight_pin_zero N d (fun _ v => g c₀ v)
        simpa using this
      rw [Finset.sum_congr rfl (fun c₀ _ => step c₀)]
      simp only [Fin.val_zero, pow_zero, Nat.sub_zero, Nat.add_sub_cancel, Matrix.one_apply]
      fin_cases c <;> simp [Fin.sum_univ_three] <;> try ring
    · -- the pinned edge is further along: peel the first letter
      intro q
      rw [← Equiv.sum_comp (consEq N)
        (fun a => pathWeight a *
          (if a q.succ.castSucc = c then
              (if a q.succ.succ = d then g (a 0) (a (Fin.last (N + 1))) else 0)
            else 0))]
      rw [Fintype.sum_prod_type]
      have step : ∀ c₀ : Fin 3,
          (∑ b : Fin (N + 1) → Fin 3,
              pathWeight (consEq N (c₀, b)) *
                (if consEq N (c₀, b) q.succ.castSucc = c then
                    (if consEq N (c₀, b) q.succ.succ = d then
                        g (consEq N (c₀, b) 0) (consEq N (c₀, b) (Fin.last (N + 1)))
                      else 0)
                  else 0))
            = ∑ i : Fin 3, ∑ j : Fin 3,
                (onesPlus ^ (q : ℕ)) i c *
                  (onesPlus c d *
                    ((onesPlus ^ (N - 1 - (q : ℕ))) d j * (onesPlus c₀ i * g c₀ j))) := by
        intro c₀
        rw [← ih q c d (fun u v => onesPlus c₀ u * g c₀ v)]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [consEq_apply, pathWeight_cons, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ,
          Fin.cons_succ, ← Fin.succ_last, Fin.cons_succ]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun c₀ _ => step c₀)]
      have hval : ((q.succ : Fin (N + 1)) : ℕ) = (q : ℕ) + 1 := rfl
      rw [hval]
      have hsub : N + 1 - 1 - ((q : ℕ) + 1) = N - 1 - (q : ℕ) := by omega
      rw [hsub, pow_succ' onesPlus (q : ℕ)]
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      ring


/-! ### Scalar evaluation of the two-point pinned transfer sum -/

private theorem sum_three_pin (X : ℕ) (c t : Fin 3) :
    ∑ v : Fin 3, (if c = v then X + 1 else X) * (if t = v then 2 else 1)
      = 4 * X + 1 + (if t = c then 1 else 0) := by
  fin_cases c <;> fin_cases t <;> simp [Fin.sum_univ_three] <;> omega

private theorem sum_perm_three (X : ℕ) (σ : Equiv.Perm (Fin 3)) (c u : Fin 3) :
    ∑ v : Fin 3, (if c = v then X + 1 else X) * (if u = σ v then 2 else 1)
      = 4 * X + 1 + (if u = σ c then 1 else 0) := by
  rw [← Equiv.sum_comp σ.symm
    (fun v => (if c = v then X + 1 else X) * (if u = σ v then 2 else 1))]
  have hcong : ∀ v : Fin 3,
      (if c = σ.symm v then X + 1 else X) * (if u = σ (σ.symm v) then 2 else 1)
        = (if σ c = v then X + 1 else X) * (if u = v then 2 else 1) := by
    intro v
    rw [Equiv.apply_symm_apply]
    congr 1
    by_cases h : σ c = v
    · rw [if_pos h, if_pos (by rw [← h, Equiv.symm_apply_apply])]
    · rw [if_neg h, if_neg (fun hh => h (by rw [hh, Equiv.apply_symm_apply]))]
  rw [Finset.sum_congr rfl (fun v _ => hcong v), sum_three_pin X (σ c) u]

private theorem sum_outer_pin (A B : ℕ) (p w : Fin 3) :
    ∑ u : Fin 3, (if u = p then A + 1 else A) * (4 * B + 1 + (if u = w then 1 else 0))
      = 12 * A * B + 3 * A + 4 * B + 1 + (if w = p then A + 1 else A) := by
  fin_cases p <;> fin_cases w <;> simp [Fin.sum_univ_three] <;> ring

/-- The scalar evaluation of the pinned double sum: `(J+I)^s` on the left of the pin,
`(J+I)^t` on the right, and the closing weight `J + P_σ` between the two ends. -/
theorem pinned_double_sum (A B K : ℕ) (σ : Equiv.Perm (Fin 3)) (p q : Fin 3) :
    (∑ u : Fin 3, ∑ v : Fin 3,
        (if u = p then A + 1 else A) *
          (K * ((if q = v then B + 1 else B) * (if u = σ v then 2 else 1))))
      = K * (12 * A * B + 4 * A + 4 * B + 1 + (if p = σ q then 1 else 0)) := by
  have hinner : ∀ u : Fin 3,
      (∑ v : Fin 3, (if u = p then A + 1 else A) *
          (K * ((if q = v then B + 1 else B) * (if u = σ v then 2 else 1))))
        = K * ((if u = p then A + 1 else A) * (4 * B + 1 + (if u = σ q then 1 else 0))) := by
    intro u
    calc (∑ v : Fin 3, (if u = p then A + 1 else A) *
            (K * ((if q = v then B + 1 else B) * (if u = σ v then 2 else 1))))
        = ((if u = p then A + 1 else A) * K) *
            ∑ v : Fin 3, ((if q = v then B + 1 else B) * (if u = σ v then 2 else 1)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ = ((if u = p then A + 1 else A) * K) * (4 * B + 1 + (if u = σ q then 1 else 0)) := by
          rw [sum_perm_three B σ q u]
      _ = K * ((if u = p then A + 1 else A) * (4 * B + 1 + (if u = σ q then 1 else 0))) := by
          ring
  rw [Finset.sum_congr rfl (fun u _ => hinner u), ← Finset.mul_sum,
    sum_outer_pin A B p (σ q)]
  by_cases h : p = σ q
  · rw [if_pos h, if_pos h.symm]; ring
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]; ring

/-! ### The correction term with two pins -/

private theorem corr_two_pin {N : ℕ} (σ : Equiv.Perm (Fin 3)) (r s : Fin (N + 1)) (p q : Fin 3) :
    (∑ a : Fin (N + 1) → Fin 3,
        (if a r = p then
          (if a s = q then (if (∀ i, a i = a 0) ∧ σ (a 0) ≠ a 0 then 1 else 0) else 0)
         else 0))
      = if p = q ∧ σ p ≠ p then 1 else 0 := by
  classical
  rw [Finset.sum_eq_single (fun _ : Fin (N + 1) => p)]
  · by_cases h : p = q ∧ σ p ≠ p
    · obtain ⟨h1, h2⟩ := h
      subst h1
      simp [h2]
    · rw [if_neg h]
      by_cases h1 : p = q
      · subst h1
        have h2 : ¬ (σ p ≠ p) := fun hh => h ⟨rfl, hh⟩
        simp at h2
        simp [h2]
      · simp [h1]
  · intro a _ hane
    by_cases h1 : a r = p
    · by_cases h2 : a s = q
      · by_cases h3 : (∀ i, a i = a 0) ∧ σ (a 0) ≠ a 0
        · exact absurd (funext fun i => by rw [h3.1 i, ← h3.1 r, h1]) hane
        · simp [h1, h2, h3]
      · simp [h1, h2]
    · simp [h1]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### The two pair marginals of the reference tensor -/

/-- **The ordinary pair marginal**: pinning the two ends of an ordinary edge of the terminal
cycle, the reference masses sum to the base `(2T, T)` plus the §5.3 residual `resOrd σ`. -/
theorem pairMarginal_ordinary {N : ℕ} (σ : Equiv.Perm (Fin 3)) (i : Fin (N + 1))
    (hi : i.val + 1 < N + 1) (p q : Fin 3) :
    (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)) = (p, q)), Uw σ a)
      = (if p = q then 2 * gammaPlus N else gammaPlus N) + resOrd σ p q := by
  classical
  set e : Fin N := ⟨i.val, by omega⟩ with he
  have he1 : (e.castSucc : Fin (N + 1)) = i := by apply Fin.ext; rfl
  have he2 : (e.succ : Fin (N + 1)) = i + 1 := by
    apply Fin.ext
    rw [Fin.val_add_one_of_lt (by exact Fin.lt_def.mpr (by simpa using by omega))]
    rfl
  have heval : (e : ℕ) = i.val := rfl
  -- rewrite the filter as a nested conditional in the two pinned coordinates
  rw [Finset.sum_filter]
  have hrw : ∀ a : Fin (N + 1) → Fin 3,
      (if (a i, a (i + 1)) = (p, q) then Uw σ a else 0)
        = (if a e.castSucc = p then
              (if a e.succ = q then 2 ^ hw σ a else 0) else 0)
          + (if a e.castSucc = p then
              (if a e.succ = q then
                  (if (∀ j, a j = a 0) ∧ σ (a 0) ≠ a 0 then 1 else 0) else 0) else 0) := by
    intro a
    have h1 : a e.castSucc = a i := by rw [he1]
    have h2 : a e.succ = a (i + 1) := by rw [he2]
    rw [h1, h2]
    simp only [Prod.mk.injEq, Uw]
    by_cases hA : a i = p <;> by_cases hB : a (i + 1) = q <;> simp [hA, hB]
  rw [Finset.sum_congr rfl (fun a _ => hrw a), Finset.sum_add_distrib]
  -- the correction half
  rw [corr_two_pin σ e.castSucc e.succ p q]
  -- the `2 ^ h` half, by the two-point pinned transfer sum
  have hmain : (∑ a : Fin (N + 1) → Fin 3,
        (if a e.castSucc = p then (if a e.succ = q then 2 ^ hw σ a else 0) else 0))
      = ∑ u : Fin 3, ∑ v : Fin 3,
          (onesPlus ^ (e : ℕ)) u p *
            (onesPlus p q * ((onesPlus ^ (N - 1 - (e : ℕ))) q v * (if u = σ v then 2 else 1))) := by
    rw [← sum_pathWeight_pin_two N e p q (fun u v => if u = σ v then 2 else 1)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [two_pow_hw]
    split_ifs <;> ring
  rw [hmain]
  -- evaluate
  set s : ℕ := (e : ℕ) with hs
  set t : ℕ := N - 1 - s with ht
  have hst : s + t + 1 = N := by
    have h1 : s < N := e.isLt
    omega
  have hApp : ∀ u : Fin 3, (onesPlus ^ s) u p = if u = p then gammaPlus s + 1 else gammaPlus s :=
    fun u => onesPlus_pow_apply s u p
  have hBpp : ∀ v : Fin 3, (onesPlus ^ t) q v = if q = v then gammaPlus t + 1 else gammaPlus t :=
    fun v => onesPlus_pow_apply t q v
  simp only [hApp, hBpp]
  rw [pinned_double_sum (gammaPlus s) (gammaPlus t) (onesPlus p q) σ p q]
  have hgam : gammaPlus N
      = 12 * gammaPlus s * gammaPlus t + 4 * gammaPlus s + 4 * gammaPlus t + 1 := by
    rw [← hst, gammaPlus_succ, gammaPlus_add s t]; ring
  rw [← hgam, onesPlus_apply]
  exact pairOrdinary_decomp (gammaPlus N) σ p q

/-- **The closing pair marginal**, in the σ-aligned coordinates `(a (last), a 0) = (p, σ q)`:
the base `(2T, T)` plus the §5.3 residual `resClose σ = 2 P_{σ⁻¹}`. -/
theorem pairMarginal_closing {N : ℕ} (σ : Equiv.Perm (Fin 3)) (p q : Fin 3) :
    (∑ a ∈ univ.filter
        (fun a : Fin (N + 1) → Fin 3 => (a (Fin.last N), a 0) = (p, σ q)), Uw σ a)
      = (if p = q then 2 * gammaPlus N else gammaPlus N) + resClose σ p q := by
  classical
  rw [Finset.sum_filter]
  have hrw : ∀ a : Fin (N + 1) → Fin 3,
      (if (a (Fin.last N), a 0) = (p, σ q) then Uw σ a else 0)
        = pathWeight a *
            ((if a 0 = σ q then 1 else 0) *
              ((if a (Fin.last N) = p then 1 else 0) *
                (if a 0 = σ (a (Fin.last N)) then 2 else 1)))
          + (if a 0 = σ q then
                (if a (Fin.last N) = p then
                    (if (∀ j, a j = a 0) ∧ σ (a 0) ≠ a 0 then 1 else 0) else 0) else 0) := by
    intro a
    simp only [Prod.mk.injEq, Uw]
    rw [two_pow_hw]
    by_cases hA : a (Fin.last N) = p <;> by_cases hB : a 0 = σ q <;> simp [hA, hB]
  rw [Finset.sum_congr rfl (fun a _ => hrw a), Finset.sum_add_distrib]
  rw [corr_two_pin σ 0 (Fin.last N) (σ q) p]
  rw [sum_pathWeight N (fun u v =>
    (if u = σ q then 1 else 0) * ((if v = p then 1 else 0) * (if u = σ v then 2 else 1)))]
  have hApp : ∀ u v : Fin 3,
      (onesPlus ^ N) u v = if u = v then gammaPlus N + 1 else gammaPlus N :=
    fun u v => onesPlus_pow_apply N u v
  simp only [hApp]
  have hcollapse : (∑ u : Fin 3, ∑ v : Fin 3,
        (if u = v then gammaPlus N + 1 else gammaPlus N) *
          ((if u = σ q then 1 else 0) * ((if v = p then 1 else 0) * (if u = σ v then 2 else 1))))
      = (if σ q = p then gammaPlus N + 1 else gammaPlus N) *
          (if σ q = σ p then 2 else 1) := by
    rw [Finset.sum_eq_single (σ q)]
    · rw [Finset.sum_eq_single p]
      · simp
      · intro v _ hv; simp [hv]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro u _ hu
      refine Finset.sum_eq_zero fun v _ => ?_
      simp [hu]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hcollapse]
  have hown : (if σ q = σ p then (2 : ℕ) else 1) = onesPerm σ p (σ q) := by
    rw [onesPerm_apply]
  have hrest : (if σ q = p then gammaPlus N + 1 else gammaPlus N)
      = (onesPlus ^ N) (σ q) p := by
    rw [onesPlus_pow_apply]
  rw [hown, hrest, mul_comm ((onesPlus ^ N) (σ q) p) (onesPerm σ p (σ q))]
  have hcorr : (if σ q = p ∧ σ (σ q) ≠ σ q then (1 : ℕ) else 0)
      = (if p = σ q ∧ σ p ≠ p then 1 else 0) := by
    by_cases h : σ q = p
    · subst h; simp
    · rw [if_neg (fun hh => h hh.1), if_neg (fun hh => h hh.1.symm)]
  rw [hcorr]
  exact pairClosing_of_transfer N σ p q


/-! ### The identity-holonomy entropy denominator (handoff §5.6, the `∏ U^U` term) -/

/-- For the identity holonomy the constant-word correction is inert. -/
theorem Uw_one {N : ℕ} (a : Fin (N + 1) → Fin 3) :
    Uw (1 : Equiv.Perm (Fin 3)) a = 2 ^ hw (1 : Equiv.Perm (Fin 3)) a := by
  unfold Uw
  simp

/-- `h` for the identity holonomy is the number of cyclic edges the word matches. -/
theorem hw_one_eq_sum {N : ℕ} (a : Fin (N + 1) → Fin 3) :
    hw (1 : Equiv.Perm (Fin 3)) a
      = ∑ i : Fin (N + 1), (if a (i + 1) = a i then 1 else 0) := by
  rw [← hwCyc_eq_hw, hwCyc, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- Splitting a one-edge match indicator into the three pinned pairs. -/
private theorem sum_match_eq_sum_pairs {N : ℕ} (i : Fin (N + 1))
    (F : (Fin (N + 1) → Fin 3) → ℕ) :
    (∑ a : Fin (N + 1) → Fin 3, (if a (i + 1) = a i then F a else 0))
      = ∑ c : Fin 3, ∑ a ∈ univ.filter
          (fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)) = (c, c)), F a := by
  classical
  have hstep : ∀ c : Fin 3,
      (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)) = (c, c)), F a)
        = ∑ a : Fin (N + 1) → Fin 3, (if a i = c ∧ a (i + 1) = c then F a else 0) := by
    intro c
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Prod.mk.injEq]
  rw [Finset.sum_congr rfl (fun c _ => hstep c), Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (a i)]
  · by_cases h : a (i + 1) = a i
    · simp [h]
    · simp [h]
  · intro c _ hc
    exact if_neg (fun hh => hc hh.1.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Every cyclic edge carries exactly `6 (γ_N + 1)` of the identity-holonomy mass.** -/
theorem edge_mass_one {N : ℕ} (i : Fin (N + 1)) :
    (∑ a : Fin (N + 1) → Fin 3,
        (if a (i + 1) = a i then 2 ^ hw (1 : Equiv.Perm (Fin 3)) a else 0))
      = 6 * (gammaPlus N + 1) := by
  classical
  have hU : ∀ a : Fin (N + 1) → Fin 3,
      (if a (i + 1) = a i then 2 ^ hw (1 : Equiv.Perm (Fin 3)) a else 0)
        = (if a (i + 1) = a i then Uw (1 : Equiv.Perm (Fin 3)) a else 0) := by
    intro a; rw [Uw_one]
  rw [Finset.sum_congr rfl (fun a _ => hU a), sum_match_eq_sum_pairs i (Uw 1)]
  have hcell : ∀ c : Fin 3,
      (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)) = (c, c)),
          Uw (1 : Equiv.Perm (Fin 3)) a) = 2 * gammaPlus N + 2 := by
    intro c
    by_cases hlast : i = Fin.last N
    · subst hlast
      have hz : (Fin.last N : Fin (N + 1)) + 1 = 0 := by apply Fin.ext; simp
      rw [hz]
      refine Eq.trans (pairMarginal_closing (N := N) (1 : Equiv.Perm (Fin 3)) c c) ?_
      simp [resClose]
    · have hi : i.val + 1 < N + 1 := by
        have h1 : i.val ≤ N := by omega
        have h2 : i.val ≠ N := fun hh => hlast (Fin.ext hh)
        omega
      rw [pairMarginal_ordinary (1 : Equiv.Perm (Fin 3)) i hi c c]
      simp [resOrd]
  rw [Finset.sum_congr rfl (fun c _ => hcell c)]
  simp
  ring

/-- **The identity-holonomy entropy sum** `∑_a h(a) 2^{h(a)}`, in closed form. -/
theorem sum_two_pow_hw_mul_hw (N : ℕ) :
    (∑ a : Fin (N + 1) → Fin 3,
        2 ^ hw (1 : Equiv.Perm (Fin 3)) a * hw (1 : Equiv.Perm (Fin 3)) a)
      = 2 * (N + 1) * (4 ^ N + 2) := by
  classical
  have hexp : ∀ a : Fin (N + 1) → Fin 3,
      2 ^ hw (1 : Equiv.Perm (Fin 3)) a * hw (1 : Equiv.Perm (Fin 3)) a
        = ∑ i : Fin (N + 1),
            (if a (i + 1) = a i then 2 ^ hw (1 : Equiv.Perm (Fin 3)) a else 0) := by
    intro a
    rw [hw_one_eq_sum a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : a (i + 1) = a i <;> simp [h]
  rw [Finset.sum_congr rfl (fun a _ => hexp a), Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i _ => edge_mass_one (N := N) i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hg := three_mul_gammaPlus_add_one N
  have hh : 6 * (gammaPlus N + 1) = 2 * (4 ^ N + 2) := by omega
  rw [hh]
  ring

/-- **The identity-holonomy budget is an exact power of two**: `∏_a U^U = 2^{6 m (γ_N + 1)}`
with `m = N + 1` terminals.  This is what makes the identity branch close with no slack. -/
theorem prod_Uw_pow_Uw_one (N : ℕ) :
    (∏ a : Fin (N + 1) → Fin 3,
        Uw (1 : Equiv.Perm (Fin 3)) a ^ Uw (1 : Equiv.Perm (Fin 3)) a)
      = 2 ^ (6 * (N + 1) * (gammaPlus N + 1)) := by
  classical
  have hstep : ∀ a : Fin (N + 1) → Fin 3,
      Uw (1 : Equiv.Perm (Fin 3)) a ^ Uw (1 : Equiv.Perm (Fin 3)) a
        = 2 ^ (2 ^ hw (1 : Equiv.Perm (Fin 3)) a * hw (1 : Equiv.Perm (Fin 3)) a) := by
    intro a
    rw [Uw_one, ← pow_mul, Nat.mul_comm]
  rw [Finset.prod_congr rfl (fun a _ => hstep a), Finset.prod_pow_eq_pow_sum,
    sum_two_pow_hw_mul_hw N]
  congr 1
  have hg := three_mul_gammaPlus_add_one N
  have : 2 * (N + 1) * (4 ^ N + 2) = 6 * (N + 1) * (gammaPlus N + 1) := by
    have h1 : 4 ^ N + 2 = 3 * (gammaPlus N + 1) := by omega
    rw [h1]; ring
  rw [this]

end RefTensor
end ListColoring

namespace ListColoring

/-! ## The identity-holonomy branch of `cycle_gm_bound_even` -/

section Identity

open Finset SimpleGraph RefTensor

/-- The pair marginal of the reference tensor at the identity holonomy, uniformly over the
cyclic edges: base `(2T, T)` plus `2 I`. -/
theorem pairMarginal_identity {N : ℕ} (i : Fin (N + 1)) (p q : Fin 3) :
    (∑ a ∈ univ.filter (fun a : Fin (N + 1) → Fin 3 => (a i, a (i + 1)) = (p, q)),
        Uw (1 : Equiv.Perm (Fin 3)) a)
      = if p = q then 2 * gammaPlus N + 2 else gammaPlus N := by
  classical
  by_cases hlast : i = Fin.last N
  · subst hlast
    have hz : (Fin.last N : Fin (N + 1)) + 1 = 0 := by apply Fin.ext; simp
    rw [hz]
    refine Eq.trans (pairMarginal_closing (N := N) (1 : Equiv.Perm (Fin 3)) p q) ?_
    by_cases h : p = q
    · subst h; simp [resClose]
    · simp [resClose, fun hh : p = (1 : Equiv.Perm (Fin 3)) q => h hh]
  · have hi : i.val + 1 < N + 1 := by
      have h1 : i.val ≤ N := by omega
      have h2 : i.val ≠ N := fun hh => hlast (Fin.ext hh)
      omega
    rw [pairMarginal_ordinary (1 : Equiv.Perm (Fin 3)) i hi p q]
    by_cases h : p = q
    · subst h; simp [resOrd]
    · simp [resOrd, fun hh : p = (1 : Equiv.Perm (Fin 3)) q => h hh]

/-- The identity-holonomy exponent matrix, refolded into `pathDiag` and `pathOff`. -/
theorem prod_pair_identity (T : ℕ) (Z : Finset ℕ) (x : ℕ → ℕ) (a b : Fin 3 → ℕ) :
    (∏ pr : Fin 3 × Fin 3,
        pathN Z x (a pr.1) (b pr.2) ^ (if pr.1 = pr.2 then 2 * T + 2 else T))
      = pathDiag Z x a b ^ (2 * T + 2) * pathOff Z x a b ^ T := by
  rw [Fintype.prod_prod_type, pathDiag_eq, pathOff_eq]
  simp +decide only [Fin.prod_univ_three, if_true, if_false]
  ring

/-- An enumeration of a three-list reindexes any product over it. -/
theorem prod_list_eq_prod_index {A : Finset ℕ} (hA : A.card = 3) {s : Fin 3 → ℕ}
    (hmem : ∀ i, s i ∈ A) (hinj : Function.Injective s) (f : ℕ → ℕ) :
    ∏ c ∈ A, f c = ∏ i : Fin 3, f (s i) := by
  rw [← enum_image hA hmem hinj, Finset.prod_image (fun i _ j _ h => hinj h)]

theorem one_le_gammaPlus {M : ℕ} (hM : 1 ≤ M) : 1 ≤ gammaPlus M := by
  have h1 := three_mul_gammaPlus_add_one M
  have h2 : (4 : ℕ) ^ 1 ≤ 4 ^ M := Nat.pow_le_pow_right (by omega) hM
  simp only [pow_one] at h2
  omega

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The path pattern at every internal vertex of the terminal cycle, ordinary and closing
alike, under a trivial holonomy. -/
theorem isPathPattern_edge {M : ℕ} (jx : CycIx M ≃ V) (L : ListAssignment V)
    (hL : IsNListAssignment L 3) (σ : Fin (M + 1) → Fin 3 → ℕ)
    (hmem : ∀ i x, σ i x ∈ L (tv jx i)) (hinj : ∀ i, Function.Injective (σ i))
    (hchain : ∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1) (x : Fin 3),
        σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x)
    (hclose : ∀ x y : Fin 3, σ (Fin.last M) x = σ 0 y → y = x) (i : Fin (M + 1)) :
    IsPathPattern (L (iv jx i)) (σ i) (σ (i + 1)) := by
  by_cases hlast : i = Fin.last M
  · subst hlast
    have hz : (Fin.last M : Fin (M + 1)) + 1 = 0 := by apply Fin.ext; simp
    rw [hz]
    exact ⟨hL _, hinj _, hinj 0, fun p q h => (hclose p q h).symm⟩
  · have hi : i.val + 1 < M + 1 := by
      have h1 : i.val ≤ M := by omega
      have h2 : i.val ≠ M := fun hh => hlast (Fin.ext hh)
      omega
    exact isPathPattern_ordinary jx L hL σ hmem hinj hchain i hi

/-- **The master mass-weighted bound at the identity holonomy** (handoff (5.19)): the
mass-weighted product of the word weights dominates `(∏ W)^{3E}` times the entropy denominator
`∏ U^U`, with *equality of the two-powers* — the terminal half is `terminal_exponent` and
`hdom`, the internal half is `path_identity_vertex` at every vertex, and the `2`-powers match
`prod_Uw_pow_Uw_one` exactly. -/
theorem master_bound_identity {M : ℕ} (hM : 1 ≤ M) (jx : CycIx M ≃ V)
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c)
    (σ : Fin (M + 1) → Fin 3 → ℕ)
    (hmem : ∀ i x, σ i x ∈ L (tv jx i)) (hinj : ∀ i, Function.Injective (σ i))
    (hchain : ∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1) (x : Fin 3),
        σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x)
    (hclose : ∀ x y : Fin 3, σ (Fin.last M) x = σ 0 y → y = x) :
    (∏ v, W v) ^ (3 * (4 * gammaPlus M + 2)) *
        ∏ g : Fin (M + 1) → Fin 3,
          Uw (1 : Equiv.Perm (Fin 3)) g ^ Uw (1 : Equiv.Perm (Fin 3)) g
      ≤ ∏ g : Fin (M + 1) → Fin 3,
          ((∏ i, w (tv jx i) (σ i (g i))) *
            ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))))
          ^ Uw (1 : Equiv.Perm (Fin 3)) g := by
  classical
  have hT : 1 ≤ gammaPlus M := one_le_gammaPlus hM
  -- split the word weight into its terminal and internal halves
  have hsplit : (∏ g : Fin (M + 1) → Fin 3,
        ((∏ i, w (tv jx i) (σ i (g i))) *
          ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))))
        ^ Uw (1 : Equiv.Perm (Fin 3)) g)
      = (∏ g : Fin (M + 1) → Fin 3,
            (∏ i, w (tv jx i) (σ i (g i))) ^ Uw (1 : Equiv.Perm (Fin 3)) g) *
        (∏ g : Fin (M + 1) → Fin 3,
            (∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))))
              ^ Uw (1 : Equiv.Perm (Fin 3)) g) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun g _ => mul_pow _ _ _
  rw [hsplit, terminal_exponent (1 : Equiv.Perm (Fin 3))
      (fun i c => w (tv jx i) (σ i c)),
    pair_exponent (1 : Equiv.Perm (Fin 3))
      (fun i p q => pathN (L (iv jx i)) (w (iv jx i)) (σ i p) (σ (i + 1) q))]
  -- the terminal half
  have hterm : (∏ i : Fin (M + 1), W (tv jx i)) ^ (3 * (4 * gammaPlus M + 2))
      ≤ ∏ i : Fin (M + 1), ∏ c : Fin 3,
          w (tv jx i) (σ i c) ^ (4 * gammaPlus M + 2) := by
    rw [← Finset.prod_pow]
    refine Finset.prod_le_prod' fun i _ => ?_
    have h1 : ∏ c ∈ L (tv jx i), w (tv jx i) c = ∏ c : Fin 3, w (tv jx i) (σ i c) :=
      prod_list_eq_prod_index (hL _) (hmem i) (hinj i) _
    calc W (tv jx i) ^ (3 * (4 * gammaPlus M + 2))
        = (W (tv jx i) ^ 3) ^ (4 * gammaPlus M + 2) := by rw [← pow_mul]
      _ ≤ (∏ c ∈ L (tv jx i), w (tv jx i) c) ^ (4 * gammaPlus M + 2) :=
          Nat.pow_le_pow_left (hdom _) _
      _ = (∏ c : Fin 3, w (tv jx i) (σ i c)) ^ (4 * gammaPlus M + 2) := by rw [h1]
      _ = ∏ c : Fin 3, w (tv jx i) (σ i c) ^ (4 * gammaPlus M + 2) :=
          (Finset.prod_pow _ _ _).symm
  -- the internal half, vertex by vertex
  have hvert : ∀ i : Fin (M + 1),
      2 ^ (6 * gammaPlus M + 6) * W (iv jx i) ^ (3 * (4 * gammaPlus M + 2))
        ≤ ∏ pr : Fin 3 × Fin 3,
            pathN (L (iv jx i)) (w (iv jx i)) (σ i pr.1) (σ (i + 1) pr.2) ^
              (∑ a ∈ univ.filter
                (fun a : Fin (M + 1) → Fin 3 => (a i, a (i + 1)) = pr),
                Uw (1 : Equiv.Perm (Fin 3)) a) := by
    intro i
    have hD : ∀ pr : Fin 3 × Fin 3,
        (∑ a ∈ univ.filter (fun a : Fin (M + 1) → Fin 3 => (a i, a (i + 1)) = pr),
            Uw (1 : Equiv.Perm (Fin 3)) a)
          = if pr.1 = pr.2 then 2 * gammaPlus M + 2 else gammaPlus M := by
      rintro ⟨p, q⟩
      exact pairMarginal_identity i p q
    rw [Finset.prod_congr rfl (fun pr _ => by rw [hD pr]),
      prod_pair_identity (gammaPlus M) (L (iv jx i)) (w (iv jx i)) (σ i) (σ (i + 1))]
    have hpp := path_identity_vertex (x := w (iv jx i))
      (isPathPattern_edge jx L hL σ hmem hinj hchain hclose i) (gammaPlus M) hT
    calc 2 ^ (6 * gammaPlus M + 6) * W (iv jx i) ^ (3 * (4 * gammaPlus M + 2))
        = 2 ^ (6 * gammaPlus M + 6) *
            (W (iv jx i) ^ 3) ^ (4 * gammaPlus M + 2) := by rw [← pow_mul]
      _ ≤ 2 ^ (6 * gammaPlus M + 6) *
            (∏ c ∈ L (iv jx i), w (iv jx i) c) ^ (4 * gammaPlus M + 2) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hdom _) _)
      _ ≤ _ := hpp
  have hint : 2 ^ ((M + 1) * (6 * gammaPlus M + 6)) *
        (∏ i : Fin (M + 1), W (iv jx i)) ^ (3 * (4 * gammaPlus M + 2))
      ≤ ∏ i : Fin (M + 1), ∏ pr : Fin 3 × Fin 3,
          pathN (L (iv jx i)) (w (iv jx i)) (σ i pr.1) (σ (i + 1) pr.2) ^
            (∑ a ∈ univ.filter
              (fun a : Fin (M + 1) → Fin 3 => (a i, a (i + 1)) = pr),
              Uw (1 : Equiv.Perm (Fin 3)) a) := by
    rw [← Finset.prod_pow]
    calc 2 ^ ((M + 1) * (6 * gammaPlus M + 6)) *
          ∏ i : Fin (M + 1), W (iv jx i) ^ (3 * (4 * gammaPlus M + 2))
        = ∏ i : Fin (M + 1),
            (2 ^ (6 * gammaPlus M + 6) * W (iv jx i) ^ (3 * (4 * gammaPlus M + 2))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← pow_mul, Nat.mul_comm (6 * gammaPlus M + 6) (M + 1)]
      _ ≤ _ := Finset.prod_le_prod' fun i _ => hvert i
  -- put the two halves together
  have hWsplit : (∏ v, W v) = (∏ i : Fin (M + 1), W (tv jx i)) *
      (∏ i : Fin (M + 1), W (iv jx i)) := by
    rw [← Equiv.prod_comp jx (fun v => W v), Fintype.prod_sum_type]
    rfl
  have hUeq : (∏ g : Fin (M + 1) → Fin 3,
        Uw (1 : Equiv.Perm (Fin 3)) g ^ Uw (1 : Equiv.Perm (Fin 3)) g)
      = 2 ^ ((M + 1) * (6 * gammaPlus M + 6)) := by
    rw [prod_Uw_pow_Uw_one M]
    congr 1
    ring
  rw [hUeq, hWsplit, mul_pow]
  calc ((∏ i : Fin (M + 1), W (tv jx i)) ^ (3 * (4 * gammaPlus M + 2)) *
          (∏ i : Fin (M + 1), W (iv jx i)) ^ (3 * (4 * gammaPlus M + 2))) *
        2 ^ ((M + 1) * (6 * gammaPlus M + 6))
      = (∏ i : Fin (M + 1), W (tv jx i)) ^ (3 * (4 * gammaPlus M + 2)) *
          (2 ^ ((M + 1) * (6 * gammaPlus M + 6)) *
            (∏ i : Fin (M + 1), W (iv jx i)) ^ (3 * (4 * gammaPlus M + 2))) := by ring
    _ ≤ _ := Nat.mul_le_mul hterm hint

/-- **The even-cycle tensor capacity at a trivial holonomy** (handoff §5.2–§5.6, the `σ = 1`
branch): with GM-dominant weights the rooted profile of the terminal root clears the cube of
the uniform normalizer `E = 4 γ_M + 2`.  Every inequality in the chain is sharp. -/
theorem cycle_core_identity {M : ℕ} (hM : 1 ≤ M) (jx : CycIx M ≃ V)
    (hadj : ∀ x y : CycIx M, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c)
    (σ : Fin (M + 1) → Fin 3 → ℕ)
    (hmem : ∀ i x, σ i x ∈ L (tv jx i)) (hinj : ∀ i, Function.Injective (σ i))
    (hchain : ∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1) (x : Fin 3),
        σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x)
    (hclose : ∀ x y : Fin 3, σ (Fin.last M) x = σ 0 y → y = x) :
    ((4 * gammaPlus M + 2) * ∏ v, W v) ^ 3
      ≤ ∏ c ∈ L (tv jx 0), rootedWcol G L w (tv jx 0) c := by
  classical
  set E : ℕ := 4 * gammaPlus M + 2 with hEdef
  have hEpos : 0 < E := by rw [hEdef]; omega
  set X : (Fin (M + 1) → Fin 3) → ℕ := fun g =>
    (∏ i, w (tv jx i) (σ i (g i))) *
      ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))) with hXdef
  -- the rooted counts, in tensor coordinates
  have hR : ∀ c : Fin 3, rootedWcol G L w (tv jx 0) (σ 0 c)
      = ∑ g ∈ (univ : Finset (Fin (M + 1) → Fin 3)).filter (fun g => g 0 = c), X g :=
    fun c => rootedWcol_eq_sum_index jx hadj L hL w σ hmem hinj c
  have hprod : ∏ c ∈ L (tv jx 0), rootedWcol G L w (tv jx 0) c
      = ∏ c : Fin 3, ∑ g ∈ (univ : Finset (Fin (M + 1) → Fin 3)).filter
          (fun g => g 0 = c), X g := by
    rw [prod_list_eq_prod_index (hL _) (hmem 0) (hinj 0)
      (fun c => rootedWcol G L w (tv jx 0) c)]
    exact Finset.prod_congr rfl fun c _ => hR c
  -- the three-fibre AM–GM and the master bound
  have hfib := fibre_amgm_even (1 : Equiv.Perm (Fin 3)) X
  have hmaster := master_bound_identity hM jx L hL w W hdom σ hmem hinj hchain hclose
  have hUpos : 0 < ∏ g : Fin (M + 1) → Fin 3,
      Uw (1 : Equiv.Perm (Fin 3)) g ^ Uw (1 : Equiv.Perm (Fin 3)) g :=
    Finset.prod_pos fun g _ => Nat.pow_pos (Uw_pos _ g)
  -- chain them
  have hchainA : ((E * ∏ v, W v) ^ 3) ^ E *
        (∏ g : Fin (M + 1) → Fin 3,
          Uw (1 : Equiv.Perm (Fin 3)) g ^ Uw (1 : Equiv.Perm (Fin 3)) g)
      ≤ (∏ c : Fin 3, ∑ g ∈ (univ : Finset (Fin (M + 1) → Fin 3)).filter
            (fun g => g 0 = c), X g) ^ E *
        (∏ g : Fin (M + 1) → Fin 3,
          Uw (1 : Equiv.Perm (Fin 3)) g ^ Uw (1 : Equiv.Perm (Fin 3)) g) := by
    calc ((E * ∏ v, W v) ^ 3) ^ E *
          (∏ g : Fin (M + 1) → Fin 3,
            Uw (1 : Equiv.Perm (Fin 3)) g ^ Uw (1 : Equiv.Perm (Fin 3)) g)
        = E ^ (3 * E) *
            ((∏ v, W v) ^ (3 * E) *
              ∏ g : Fin (M + 1) → Fin 3,
                Uw (1 : Equiv.Perm (Fin 3)) g ^ Uw (1 : Equiv.Perm (Fin 3)) g) := by
          rw [← pow_mul, mul_pow]
          ring
      _ ≤ E ^ (3 * E) * ∏ g : Fin (M + 1) → Fin 3, X g ^ Uw (1 : Equiv.Perm (Fin 3)) g :=
          Nat.mul_le_mul_left _ hmaster
      _ ≤ _ := hfib
  have hcancel : ((E * ∏ v, W v) ^ 3) ^ E
      ≤ (∏ c : Fin 3, ∑ g ∈ (univ : Finset (Fin (M + 1) → Fin 3)).filter
          (fun g => g 0 = c), X g) ^ E :=
    Nat.le_of_mul_le_mul_right hchainA hUpos
  rw [hprod]
  exact (Nat.pow_le_pow_iff_left (by omega : E ≠ 0)).mp hcancel

end Identity

/-! ## The even-cycle statement in the coordinates of `cycle_gm_bound_even` -/

section Final

open Finset SimpleGraph RefTensor

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **`cycle_gm_bound_even` on the identity branch.**  For an even cycle whose terminal
enumeration chain closes with a trivial holonomy, the rooted profile clears the cube of the
uniform normalizer.  The chain is sharp: `path_cone_four_one` at every internal vertex against
`prod_Uw_pow_Uw_one`, with equality of the two-powers. -/
theorem cycle_gm_bound_even_identity {M : ℕ} (hM : 1 ≤ M)
    (ix : Fin (2 * M + 1 + 1) ≃ V)
    (hadj : ∀ i j : Fin (2 * M + 1 + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c)
    (jx : CycIx M ≃ V) (hjx : ∀ x y : CycIx M, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (hroot : tv jx 0 = ix 0)
    (σ : Fin (M + 1) → Fin 3 → ℕ)
    (hmem : ∀ i x, σ i x ∈ L (tv jx i)) (hinj : ∀ i, Function.Injective (σ i))
    (hchain : ∀ (i : Fin (M + 1)) (h : i.val + 1 < M + 1) (x : Fin 3),
        σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x)
    (hclose : ∀ x y : Fin 3, σ (Fin.last M) x = σ 0 y → y = x) :
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3
      ≤ ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c := by
  have hA : rootedCol G (constList V 3) (ix 0) 0 = 4 * gammaPlus M + 2 := by
    rw [rootedCol_constList_cycle (by omega) ix hadj,
      show 2 * M + 1 + 1 = 2 * M + 2 from rfl, uniformA_three_even]
  rw [hA, ← hroot]
  exact cycle_core_identity hM jx hjx L hL w W hdom σ hmem hinj hchain hclose

/-- **`cycle_gm_bound_even` for the four-cycle** (handoff UM-090), unconditionally: at `M = 1`
there is only one terminal pair, so the chain's own bijection closes the seam and the holonomy
is forced to be trivial (`terminal_closing_model_trivial`).  `C_4` therefore lands in the
identity branch, where the budget closes with equality. -/
theorem cycle_gm_bound_even_four' (ix : Fin (2 * 1 + 1 + 1) ≃ V)
    (hadj : ∀ i j : Fin (2 * 1 + 1 + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) :
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3
      ≤ ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c := by
  obtain ⟨jx, hjx, hroot⟩ := exists_cyc_model (M := 1) ix hadj
  obtain ⟨σ, P, hmem, hinj, hchain, -⟩ := exists_terminal_closing_model jx L hL
  have hclose := terminal_closing_model_trivial (M := 1) rfl jx L σ hmem hinj hchain
  exact cycle_gm_bound_even_identity (by omega) ix hadj L hL w W hdom jx hjx hroot σ hmem hinj
    hchain (fun x y h => by simpa using hclose x y h)

end Final

/-! ## Wrappers and remaining table arithmetic -/

section Extra

open Finset SimpleGraph RefTensor

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `cycle_gm_bound_even` (`Cacti/GMFinal.lean`) at `m = 3`, i.e. for the four-cycle. -/
theorem cycle_gm_bound_even_three {m : ℕ} (hm : m = 3) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) :
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3
      ≤ ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c := by
  subst hm
  exact cycle_gm_bound_even_four' ix hadj L hL w W hdom

/-- The closing repair, as a pure re-split of the same integer. -/
theorem close_repair_resplit {N : ℕ} (hN : 1 ≤ N) (σ : Equiv.Perm (Fin 3)) (p q : Fin 3) :
    (if p = q then 2 * gammaPlus N else gammaPlus N) + resClose σ p q
      = (if p = q then 2 * (gammaPlus N - 1) else gammaPlus N) + resCloseRepaired σ p q := by
  have hT : 1 ≤ gammaPlus N := one_le_gammaPlus hN
  simp only [resClose, resCloseRepaired, Matrix.of_apply]
  by_cases h : p = q
  · subst h; simp; omega
  · simp [h]

end Extra

/-! ## The non-identity residual assemblies (available for the σ ≠ 1 branch) -/

section Residuals

open Finset

variable {Z : Finset ℕ} {x : ℕ → ℕ} {a b : Fin 3 → ℕ}

theorem path_ordinary_threeCycle (h : IsPathPattern Z a b) (T : ℕ) :
    2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      ≤ (pathDiag Z x a b ^ (2 * T) * pathOff Z x a b ^ T) *
          (pathN Z x (a 0) (b 0) * pathN Z x (a 0) (b 2) *
            (pathN Z x (a 1) (b 0) * pathN Z x (a 1) (b 1)) *
              (pathN Z x (a 2) (b 1) * pathN Z x (a 2) (b 2))) := by
  have hbase := path_cone_pow (D := pathDiag Z x a b) (O := pathOff Z x a b)
    (X := ∏ z ∈ Z, x z) (path_cone_two_one h) (path_ray_off h) T 0
  have hres := path_residual_three_cycle_ordinary (x := x) h
  calc 2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      = (2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2 * 0)) * (∏ z ∈ Z, x z) ^ 2 := by ring
    _ ≤ ((pathDiag Z x a b ^ 2 * pathOff Z x a b) ^ T * pathOff Z x a b ^ 0) * _ :=
        Nat.mul_le_mul hbase hres
    _ = _ := by rw [mul_pow, ← pow_mul]; ring




/-- Transposition seam, **repaired** base `(2T-2, T)` with `T = S+1`: `(T-1)·(2,1) + 1·(0,1)`
from `path_cone_pow`, times the `d = 4` residual `path_residual_trans_closing`. -/
theorem path_closing_trans_repaired (h : IsPathPattern Z a b) (S : ℕ) :
    2 ^ (6 * S) * (∏ z ∈ Z, x z) ^ (4 * S + 6)
      ≤ (pathDiag Z x a b ^ (2 * S) * pathOff Z x a b ^ (S + 1)) *
          (pathN Z x (a 0) (b 0) * pathN Z x (a 0) (b 1) *
            (pathN Z x (a 1) (b 0) * pathN Z x (a 1) (b 1)) *
              pathN Z x (a 2) (b 2) ^ 2) ^ 2 := by
  have hbase := path_cone_pow (D := pathDiag Z x a b) (O := pathOff Z x a b)
    (X := ∏ z ∈ Z, x z) (path_cone_two_one h) (path_ray_off h) S 1
  have hres := path_residual_trans_closing (x := x) h
  calc 2 ^ (6 * S) * (∏ z ∈ Z, x z) ^ (4 * S + 6)
      = (2 ^ (6 * S) * (∏ z ∈ Z, x z) ^ (4 * S + 2 * 1)) * (∏ z ∈ Z, x z) ^ 4 := by ring
    _ ≤ ((pathDiag Z x a b ^ 2 * pathOff Z x a b) ^ S * pathOff Z x a b ^ 1) * _ :=
        Nat.mul_le_mul hbase hres
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Transposition, ordinary edge. -/
theorem path_ordinary_trans (h : IsPathPattern Z a b) (T : ℕ) :
    2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      ≤ (pathDiag Z x a b ^ (2 * T) * pathOff Z x a b ^ T) *
          (pathN Z x (a 0) (b 0) * pathN Z x (a 0) (b 1) *
            (pathN Z x (a 1) (b 0) * pathN Z x (a 1) (b 1)) *
              pathN Z x (a 2) (b 2) ^ 2) := by
  have hbase := path_cone_pow (D := pathDiag Z x a b) (O := pathOff Z x a b)
    (X := ∏ z ∈ Z, x z) (path_cone_two_one h) (path_ray_off h) T 0
  have hres := path_residual_trans_ordinary (x := x) h
  calc 2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      = (2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2 * 0)) * (∏ z ∈ Z, x z) ^ 2 := by ring
    _ ≤ ((pathDiag Z x a b ^ 2 * pathOff Z x a b) ^ T * pathOff Z x a b ^ 0) * _ :=
        Nat.mul_le_mul hbase hres
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Three-cycle seam (no repair needed), `d = 2` residual stated halved. -/
theorem path_closing_threeCycle (h : IsPathPattern Z a b) (T : ℕ) :
    2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      ≤ (pathDiag Z x a b ^ (2 * T) * pathOff Z x a b ^ T) *
          (pathN Z x (a 0) (b 2) * pathN Z x (a 1) (b 0) * pathN Z x (a 2) (b 1)) ^ 2 := by
  have hbase := path_cone_pow (D := pathDiag Z x a b) (O := pathOff Z x a b)
    (X := ∏ z ∈ Z, x z) (path_cone_two_one h) (path_ray_off h) T 0
  have hres := path_residual_three_cycle_closing (x := x) h
  have hres2 : (∏ z ∈ Z, x z) ^ 2
      ≤ (pathN Z x (a 0) (b 2) * pathN Z x (a 1) (b 0) * pathN Z x (a 2) (b 1)) ^ 2 :=
    Nat.pow_le_pow_left hres 2
  calc 2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2)
      = (2 ^ (6 * T) * (∏ z ∈ Z, x z) ^ (4 * T + 2 * 0)) * (∏ z ∈ Z, x z) ^ 2 := by ring
    _ ≤ ((pathDiag Z x a b ^ 2 * pathOff Z x a b) ^ T * pathOff Z x a b ^ 0) * _ :=
        Nat.mul_le_mul hbase hres2
    _ = _ := by rw [mul_pow, ← pow_mul]; ring


end Residuals

end ListColoring




namespace ListColoring

open Finset SimpleGraph RefTensor

/-! # UM-096: the `C₆` base case of `cycle_gm_bound_even` (the non-identity holonomy branch) -/

/-! ## 1.  The reference mass tables of `C₆` -/

section Tables

/-- **The two `C₆` mass tables of UM-096**, laid out as one lookup indexed by the two values
`t 0, t 1` that determine the holonomy permutation `t`.  For a transposition seam the multiset of
entries is `1^6 2^10 3^6 4^4 6^1` (entropy `2^58·3^24`), for a three-cycle seam `1^8 2^6 3^6 4^7`
(entropy `2^68·3^18`).  Every one-coordinate marginal is `E = 22`, the total mass is `P = 66`, and
all three pair marginals are exactly the `(M,S) = (10,6)` base composed with the holonomy. -/
def c6tbl : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=
  ![
    ![
      -- `t 0 = 0`, `t 1 = 0`
      ![![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]],
        ![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]],
        ![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]]],
      -- `t 0 = 0`, `t 1 = 1`
      ![![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]],
        ![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]],
        ![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]]],
      -- `t 0 = 0`, `t 1 = 2`
      ![![![6, 2, 2], ![2, 2, 2], ![2, 2, 2]],
        ![![2, 1, 3], ![3, 4, 3], ![1, 1, 4]],
        ![![2, 3, 1], ![1, 4, 1], ![3, 3, 4]]]
    ],
    ![
      -- `t 0 = 1`, `t 1 = 0`
      ![![![3, 4, 3], ![1, 4, 1], ![2, 2, 2]],
        ![![4, 1, 1], ![4, 3, 3], ![2, 2, 2]],
        ![![3, 1, 2], ![1, 3, 2], ![2, 2, 6]]],
      -- `t 0 = 1`, `t 1 = 1`
      ![![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]],
        ![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]],
        ![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]]],
      -- `t 0 = 1`, `t 1 = 2`
      ![![![3, 3, 4], ![1, 2, 3], ![2, 1, 3]],
        ![![4, 1, 1], ![4, 4, 2], ![2, 1, 3]],
        ![![3, 2, 1], ![1, 4, 1], ![2, 4, 4]]]
    ],
    ![
      -- `t 0 = 2`, `t 1 = 0`
      ![![![3, 4, 3], ![1, 4, 1], ![2, 2, 2]],
        ![![3, 1, 2], ![2, 4, 4], ![1, 1, 4]],
        ![![4, 1, 1], ![3, 2, 1], ![3, 3, 4]]],
      -- `t 0 = 2`, `t 1 = 1`
      ![![![3, 3, 4], ![2, 2, 2], ![1, 1, 4]],
        ![![3, 2, 1], ![2, 6, 2], ![1, 2, 3]],
        ![![4, 1, 1], ![2, 2, 2], ![4, 3, 3]]],
      -- `t 0 = 2`, `t 1 = 2`
      ![![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]],
        ![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]],
        ![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]]]
    ]
  ]

/-- The reference masses of `C₆` at a holonomy given by the function `t`. -/
def c6mass (t : Fin 3 → Fin 3) (g : Fin 3 → Fin 3) : ℕ := c6tbl (t 0) (t 1) (g 0) (g 1) (g 2)

theorem c6mass_pos (t : Fin 3 → Fin 3) (g : Fin 3 → Fin 3) : 0 < c6mass t g := by
  revert t g; decide +kernel

/-- Every one-coordinate marginal is `E = 22`. -/
theorem c6mass_marg (t : Fin 3 → Fin 3) (ht : Function.Injective t) (hne : ∃ x, t x ≠ x)
    (i : Fin 3) (c : Fin 3) :
    (∑ g ∈ (univ : Finset (Fin 3 → Fin 3)).filter (fun g => g i = c), c6mass t g) = 22 := by
  revert t i c; decide +kernel

/-- The pair marginal on the first ordinary edge: the `(10,6)` base on the identity matching. -/
theorem c6mass_pair0 (t : Fin 3 → Fin 3) (ht : Function.Injective t) (hne : ∃ x, t x ≠ x)
    (pr : Fin 3 × Fin 3) :
    (∑ g ∈ (univ : Finset (Fin 3 → Fin 3)).filter
        (fun g => (g (0 : Fin 3), g ((0 : Fin 3) + 1)) = pr), c6mass t g)
      = if pr.1 = pr.2 then 10 else 6 := by
  revert t pr; decide +kernel

/-- The pair marginal on the second ordinary edge. -/
theorem c6mass_pair1 (t : Fin 3 → Fin 3) (ht : Function.Injective t) (hne : ∃ x, t x ≠ x)
    (pr : Fin 3 × Fin 3) :
    (∑ g ∈ (univ : Finset (Fin 3 → Fin 3)).filter
        (fun g => (g (1 : Fin 3), g ((1 : Fin 3) + 1)) = pr), c6mass t g)
      = if pr.1 = pr.2 then 10 else 6 := by
  revert t pr; decide +kernel

/-- The pair marginal on the closing edge: the `(10,6)` base composed with the holonomy `t`. -/
theorem c6mass_pair2 (t : Fin 3 → Fin 3) (ht : Function.Injective t) (hne : ∃ x, t x ≠ x)
    (pr : Fin 3 × Fin 3) :
    (∑ g ∈ (univ : Finset (Fin 3 → Fin 3)).filter
        (fun g => (g (2 : Fin 3), g ((2 : Fin 3) + 1)) = pr), c6mass t g)
      = if pr.2 = t pr.1 then 10 else 6 := by
  revert t pr; decide +kernel

/-- **The entropy comparison of UM-096.**  The entropy denominator of either table is paid by the
budget `2^50·3^30` of two plain `(10,6)` cone points and one strict one. -/
theorem c6mass_entropy (t : Fin 3 → Fin 3) (ht : Function.Injective t) (hne : ∃ x, t x ≠ x) :
    (∏ g : Fin 3 → Fin 3, c6mass t g ^ c6mass t g) ≤ 2 ^ 50 * 3 ^ 30 := by
  revert t; decide +kernel

end Tables

/-! ## 2.  The generic tensor bookkeeping (`RefTensor` with an arbitrary mass table) -/

section Generic

/-- `terminal_exponent` for an arbitrary mass table with uniform one-coordinate marginals. -/
theorem terminal_exponent_gen (U : (Fin 3 → Fin 3) → ℕ) (E : ℕ)
    (hmarg : ∀ (i : Fin 3) (c : Fin 3),
      (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a i = c), U a) = E)
    (y : Fin 3 → Fin 3 → ℕ) :
    ∏ a : Fin 3 → Fin 3, (∏ i, y i (a i)) ^ U a
      = ∏ i : Fin 3, ∏ c : Fin 3, (y i c) ^ E := by
  classical
  have hstep : ∀ i : Fin 3,
      ∏ a : Fin 3 → Fin 3, (y i (a i)) ^ U a = ∏ c : Fin 3, (y i c) ^ E := by
    intro i
    rw [← Finset.prod_fiberwise_of_maps_to (g := fun a : Fin 3 → Fin 3 => a i)
      (t := (univ : Finset (Fin 3))) (fun a _ => Finset.mem_univ (a i))
      (fun a => (y i (a i)) ^ U a)]
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [Finset.prod_congr rfl (fun a ha => by rw [(Finset.mem_filter.mp ha).2] :
      ∀ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a i = c),
        (y i (a i)) ^ U a = (y i c) ^ U a)]
    rw [Finset.prod_pow_eq_pow_sum, hmarg i c]
  calc ∏ a : Fin 3 → Fin 3, (∏ i, y i (a i)) ^ U a
      = ∏ a : Fin 3 → Fin 3, ∏ i, (y i (a i)) ^ U a :=
        Finset.prod_congr rfl fun a _ => (Finset.prod_pow _ _ _).symm
    _ = ∏ i : Fin 3, ∏ a : Fin 3 → Fin 3, (y i (a i)) ^ U a := Finset.prod_comm
    _ = ∏ i : Fin 3, ∏ c : Fin 3, (y i c) ^ E :=
        Finset.prod_congr rfl fun i _ => hstep i

/-- `pair_exponent` for an arbitrary mass table. -/
theorem pair_exponent_gen (U : (Fin 3 → Fin 3) → ℕ)
    (z : Fin 3 → Fin 3 → Fin 3 → ℕ) :
    ∏ a : Fin 3 → Fin 3, (∏ i, z i (a i) (a (i + 1))) ^ U a
      = ∏ i : Fin 3, ∏ p : Fin 3 × Fin 3, (z i p.1 p.2) ^
          (∑ a ∈ univ.filter
            (fun a : Fin 3 → Fin 3 => (a i, a (i + 1)) = p), U a) := by
  classical
  have hstep : ∀ i : Fin 3,
      ∏ a : Fin 3 → Fin 3, (z i (a i) (a (i + 1))) ^ U a
        = ∏ p : Fin 3 × Fin 3, (z i p.1 p.2) ^
            (∑ a ∈ univ.filter
              (fun a : Fin 3 → Fin 3 => (a i, a (i + 1)) = p), U a) := by
    intro i
    rw [← Finset.prod_fiberwise_of_maps_to
      (g := fun a : Fin 3 → Fin 3 => (a i, a (i + 1)))
      (t := (univ : Finset (Fin 3 × Fin 3))) (fun a _ => Finset.mem_univ _)
      (fun a => (z i (a i) (a (i + 1))) ^ U a)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Finset.prod_congr rfl (fun a ha => by
      have h := (Finset.mem_filter.mp ha).2
      rw [show a i = p.1 from congrArg Prod.fst h, show a (i + 1) = p.2 from congrArg Prod.snd h] :
      ∀ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => (a i, a (i + 1)) = p),
        (z i (a i) (a (i + 1))) ^ U a = (z i p.1 p.2) ^ U a)]
    rw [Finset.prod_pow_eq_pow_sum]
  calc ∏ a : Fin 3 → Fin 3, (∏ i, z i (a i) (a (i + 1))) ^ U a
      = ∏ a : Fin 3 → Fin 3, ∏ i, (z i (a i) (a (i + 1))) ^ U a :=
        Finset.prod_congr rfl fun a _ => (Finset.prod_pow _ _ _).symm
    _ = ∏ i : Fin 3, ∏ a : Fin 3 → Fin 3, (z i (a i) (a (i + 1))) ^ U a :=
        Finset.prod_comm
    _ = _ := Finset.prod_congr rfl fun i _ => hstep i

/-- `fibre_amgm_even` for an arbitrary positive mass table with uniform root marginals. -/
theorem fibre_amgm_gen (U : (Fin 3 → Fin 3) → ℕ) (E : ℕ) (hE : 0 < E)
    (hmarg : ∀ c : Fin 3,
      (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a 0 = c), U a) = E)
    (hpos : ∀ a, 0 < U a) (X : (Fin 3 → Fin 3) → ℕ) :
    E ^ (3 * E) * ∏ a : Fin 3 → Fin 3, X a ^ U a
      ≤ (∏ c : Fin 3, ∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a 0 = c), X a) ^ E
        * ∏ a : Fin 3 → Fin 3, (U a) ^ (U a) := by
  classical
  have hfib : ∀ c : Fin 3,
      E ^ E * ∏ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a 0 = c), X a ^ U a
        ≤ (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a 0 = c), X a) ^ E
          * ∏ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a 0 = c), (U a) ^ (U a) := by
    intro c
    exact weighted_amgm_masses _ X U hE (hmarg c) (fun a _ => hpos a)
  have hmul := Finset.prod_le_prod' (s := (univ : Finset (Fin 3))) (fun c _ => hfib c)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← pow_mul, Finset.prod_mul_distrib] at hmul
  have hXfib : ∏ c : Fin 3, ∏ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a 0 = c),
      X a ^ U a = ∏ a : Fin 3 → Fin 3, X a ^ U a :=
    Finset.prod_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (a 0)) _
  have hUfib : ∏ c : Fin 3, ∏ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a 0 = c),
      (U a) ^ (U a) = ∏ a : Fin 3 → Fin 3, (U a) ^ (U a) :=
    Finset.prod_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (a 0)) _
  have hpowfib : ∏ c : Fin 3,
      (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a 0 = c), X a) ^ E
      = (∏ c : Fin 3, ∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a 0 = c), X a) ^ E :=
    Finset.prod_pow _ _ _
  rw [hXfib, hUfib, hpowfib] at hmul
  rw [Nat.mul_comm 3 E]
  exact hmul

end Generic

/-! ## 3.  The `(10,6)` cone points, plain and strict -/

section Cone

variable {Z : Finset ℕ} {a b : Fin 3 → ℕ}

/-- The plain `(M,S) = (10,6)` cone point: `(0,1) + 5·(2,1)`, constant `2^30`. -/
theorem c6_edge_nonstrict (h : IsPathPattern Z a b) (x : ℕ → ℕ) :
    2 ^ 30 * (∏ z ∈ Z, x z) ^ 22 ≤ pathDiag Z x a b ^ 10 * pathOff Z x a b ^ 6 := by
  have hh := path_cone_pow (D := pathDiag Z x a b) (O := pathOff Z x a b)
    (X := ∏ z ∈ Z, x z) (path_cone_two_one h) (path_ray_off h) 5 1
  calc 2 ^ 30 * (∏ z ∈ Z, x z) ^ 22
      = 2 ^ (6 * 5) * (∏ z ∈ Z, x z) ^ (4 * 5 + 2 * 1) := by norm_num
    _ ≤ (pathDiag Z x a b ^ 2 * pathOff Z x a b) ^ 5 * pathOff Z x a b ^ 1 := hh
    _ = pathDiag Z x a b ^ 10 * pathOff Z x a b ^ 6 := by ring

/-- The strict `(M,S) = (10,6)` cone point on an unequal-list path: constant `3^30 / 2^10`,
which beats `2^30` by `(729/256)^5`.  This is the resource UM-096 spends. -/
theorem c6_edge_strict (h : IsPathPattern Z a b) (x : ℕ → ℕ) (hne : a ≠ b) :
    3 ^ 30 * (∏ z ∈ Z, x z) ^ 22
      ≤ 2 ^ 10 * (pathDiag Z x a b ^ 10 * pathOff Z x a b ^ 6) := by
  have hh := path_strict_pow (D := pathDiag Z x a b) (O := pathOff Z x a b)
    (X := ∏ z ∈ Z, x z) (path_cone_two_one_strict h x hne) (path_ray_off h) 5 1
  calc 3 ^ 30 * (∏ z ∈ Z, x z) ^ 22
      = 729 ^ 5 * (∏ z ∈ Z, x z) ^ (4 * 5 + 2 * 1) := by norm_num
    _ ≤ 4 ^ 5 * ((pathDiag Z x a b ^ 2 * pathOff Z x a b) ^ 5 * pathOff Z x a b ^ 1) := hh
    _ = 2 ^ 10 * (pathDiag Z x a b ^ 10 * pathOff Z x a b ^ 6) := by ring

/-- Two plain cone points and one strict one. -/
theorem c6_three_edges {A0 A1 A2 B0 B1 B2 : ℕ}
    (h0 : 2 ^ 30 * A0 ≤ B0) (h1 : 2 ^ 30 * A1 ≤ B1) (h2 : 3 ^ 30 * A2 ≤ 2 ^ 10 * B2) :
    2 ^ 60 * 3 ^ 30 * (A0 * A1 * A2) ≤ 2 ^ 10 * (B0 * B1 * B2) := by
  calc 2 ^ 60 * 3 ^ 30 * (A0 * A1 * A2) = (2 ^ 30 * A0) * (2 ^ 30 * A1) * (3 ^ 30 * A2) := by ring
    _ ≤ B0 * B1 * (2 ^ 10 * B2) := Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2
    _ = 2 ^ 10 * (B0 * B1 * B2) := by ring

/-- The `(M,S)` exponent matrix on a matched edge, refolded into `pathDiag` and `pathOff`. -/
theorem prod_pair_base (Z : Finset ℕ) (x : ℕ → ℕ) (a b : Fin 3 → ℕ) (M S : ℕ) :
    (∏ pr : Fin 3 × Fin 3, pathN Z x (a pr.1) (b pr.2) ^ (if pr.1 = pr.2 then M else S))
      = pathDiag Z x a b ^ M * pathOff Z x a b ^ S := by
  rw [Fintype.prod_prod_type, pathDiag_eq, pathOff_eq]
  simp +decide only [Fin.prod_univ_three, if_true, if_false]
  ring

/-- The same on the closing edge, where the matching is the holonomy `P`. -/
theorem prod_pair_close (Z : Finset ℕ) (x : ℕ → ℕ) (s2 s0 : Fin 3 → ℕ)
    (P : Equiv.Perm (Fin 3)) (M S : ℕ) :
    (∏ pr : Fin 3 × Fin 3, pathN Z x (s2 pr.1) (s0 pr.2) ^ (if pr.2 = P pr.1 then M else S))
      = pathDiag Z x s2 (fun q => s0 (P q)) ^ M * pathOff Z x s2 (fun q => s0 (P q)) ^ S := by
  rw [← prod_pair_base Z x s2 (fun q => s0 (P q)) M S]
  refine Fintype.prod_equiv (Equiv.prodCongr (Equiv.refl (Fin 3)) P.symm) _ _ ?_
  rintro ⟨u, v⟩
  have h1 : P (P.symm v) = v := P.apply_symm_apply v
  have h2 : (u = P.symm v) ↔ (v = P u) :=
    ⟨fun hh => by rw [hh, h1], fun hh => by rw [hh, P.symm_apply_apply]⟩
  show pathN Z x (s2 u) (s0 v) ^ (if v = P u then M else S)
      = pathN Z x (s2 u) (s0 (P (P.symm v))) ^ (if u = P.symm v then M else S)
  rw [h1]
  by_cases huv : v = P u
  · rw [if_pos huv, if_pos (h2.mpr huv)]
  · rw [if_neg huv, if_neg (fun hh => huv (h2.mp hh))]

end Cone

end ListColoring

namespace ListColoring

open Finset SimpleGraph RefTensor

/-! ## 4.  The `C₆` core at a nontrivial holonomy -/

section Core

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An enumeration of a three-list reindexes any product over it. -/
theorem prod_list_eq_prod_index' {A : Finset ℕ} (hA : A.card = 3) {s : Fin 3 → ℕ}
    (hmem : ∀ i, s i ∈ A) (hinj : Function.Injective s) (f : ℕ → ℕ) :
    ∏ c ∈ A, f c = ∏ i : Fin 3, f (s i) := by
  rw [← enum_image hA hmem hinj, Finset.prod_image (fun i _ j _ h => hinj h)]

/-- **A nontrivial holonomy exposes an unequal internal vertex of `C₆`.** -/
theorem c6_unequal (σ : Fin 3 → Fin 3 → ℕ) (P : Equiv.Perm (Fin 3))
    (hinj : Function.Injective (σ 0)) (hP : P ≠ 1) :
    σ 0 ≠ σ 1 ∨ σ 1 ≠ σ 2 ∨ σ 2 ≠ (fun q => σ 0 (P q)) := by
  by_contra hc
  push_neg at hc
  obtain ⟨h01, h12, h20⟩ := hc
  refine hP (Equiv.ext fun q => ?_)
  have hq : σ 0 (P q) = σ 0 q := by
    have hh : σ 2 q = σ 0 (P q) := congrFun h20 q
    rw [← hh, ← h12, ← h01]
  simpa using hinj hq

/-- **UM-096, the tensor core.**  On `C₆` with a nontrivial holonomy the rooted profile of the
terminal root clears the cube of the uniform normalizer `E = 22`. -/
theorem c6_core (jx : CycIx 2 ≃ V)
    (hjx : ∀ x y : CycIx 2, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c)
    (σ : Fin 3 → Fin 3 → ℕ) (P : Equiv.Perm (Fin 3))
    (hmem : ∀ i x, σ i x ∈ L (tv jx i)) (hinj : ∀ i, Function.Injective (σ i))
    (hchain : ∀ (i : Fin 3) (h : i.val + 1 < 3) (x : Fin 3),
        σ i x ∈ L (tv jx ⟨i.val + 1, h⟩) → σ ⟨i.val + 1, h⟩ x = σ i x)
    (hclose : ∀ x y : Fin 3, σ 2 x = σ 0 y → y = P x)
    (hP : P ≠ 1) :
    (22 * ∏ v, W v) ^ 3 ≤ ∏ c ∈ L (tv jx 0), rootedWcol G L w (tv jx 0) c := by
  classical
  have hlast : (Fin.last 2 : Fin 3) = 2 := by decide
  have he01 : ((0 : Fin 3) + 1) = 1 := by decide
  have he12 : ((1 : Fin 3) + 1) = 2 := by decide
  have he20 : ((2 : Fin 3) + 1) = 0 := by decide
  -- the holonomy as a plain function
  have hti : Function.Injective (fun i => P i) := P.injective
  have htn : ∃ i, (fun i => P i) i ≠ i := by
    by_contra hcon
    push_neg at hcon
    exact hP (Equiv.ext fun q => by simpa using hcon q)
  have hUpos : ∀ g, 0 < c6mass (fun i => P i) g := fun g => c6mass_pos _ g
  have hUmarg : ∀ (i c : Fin 3),
      (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => a i = c), c6mass (fun i => P i) a) = 22 :=
    fun i c => c6mass_marg _ hti htn i c
  -- the rooted counts, in tensor coordinates
  have hR : ∀ c : Fin 3, rootedWcol G L w (tv jx 0) (σ 0 c)
      = ∑ g ∈ (univ : Finset (Fin 3 → Fin 3)).filter (fun g => g 0 = c),
          ((∏ i, w (tv jx i) (σ i (g i))) *
            ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1)))) :=
    fun c => rootedWcol_eq_sum_index jx hjx L hL w σ hmem hinj c
  have hprod : ∏ c ∈ L (tv jx 0), rootedWcol G L w (tv jx 0) c
      = ∏ c : Fin 3, ∑ g ∈ (univ : Finset (Fin 3 → Fin 3)).filter (fun g => g 0 = c),
          ((∏ i, w (tv jx i) (σ i (g i))) *
            ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1)))) := by
    rw [prod_list_eq_prod_index' (hL _) (hmem 0) (hinj 0)
      (fun c => rootedWcol G L w (tv jx 0) c)]
    exact Finset.prod_congr rfl fun c _ => hR c
  -- the path patterns at the three internal vertices
  have pp0 : IsPathPattern (L (iv jx 0)) (σ 0) (σ ((0 : Fin 3) + 1)) :=
    isPathPattern_ordinary jx L hL σ hmem hinj hchain 0 (by decide)
  have pp1 : IsPathPattern (L (iv jx 1)) (σ 1) (σ ((1 : Fin 3) + 1)) :=
    isPathPattern_ordinary jx L hL σ hmem hinj hchain 1 (by decide)
  have pp2 : IsPathPattern (L (iv jx 2)) (σ 2) (fun q => σ 0 (P q)) := by
    have hh := isPathPattern_closing jx L hL σ P hinj (by rw [hlast]; exact hclose)
    rwa [hlast] at hh
  -- the weight dominance at the internal vertices
  have hWi : ∀ i : Fin 3,
      W (iv jx i) ^ 66 ≤ (∏ z ∈ L (iv jx i), w (iv jx i) z) ^ 22 := by
    intro i
    calc W (iv jx i) ^ 66 = (W (iv jx i) ^ 3) ^ 22 := by ring
      _ ≤ _ := Nat.pow_le_pow_left (hdom _) _
  have hns : ∀ (i : Fin 3) (b : Fin 3 → ℕ), IsPathPattern (L (iv jx i)) (σ i) b →
      2 ^ 30 * W (iv jx i) ^ 66
        ≤ pathDiag (L (iv jx i)) (w (iv jx i)) (σ i) b ^ 10 *
          pathOff (L (iv jx i)) (w (iv jx i)) (σ i) b ^ 6 := by
    intro i b hp
    exact le_trans (Nat.mul_le_mul_left _ (hWi i)) (c6_edge_nonstrict hp (w (iv jx i)))
  have hst : ∀ (i : Fin 3) (b : Fin 3 → ℕ), IsPathPattern (L (iv jx i)) (σ i) b → σ i ≠ b →
      3 ^ 30 * W (iv jx i) ^ 66
        ≤ 2 ^ 10 * (pathDiag (L (iv jx i)) (w (iv jx i)) (σ i) b ^ 10 *
          pathOff (L (iv jx i)) (w (iv jx i)) (σ i) b ^ 6) := by
    intro i b hp hne
    exact le_trans (Nat.mul_le_mul_left _ (hWi i)) (c6_edge_strict hp (w (iv jx i)) hne)
  -- the three edge exponent matrices, refolded
  have hedge0 : (∏ pr : Fin 3 × Fin 3,
        (pathN (L (iv jx 0)) (w (iv jx 0)) (σ 0 pr.1) (σ ((0 : Fin 3) + 1) pr.2)) ^
          (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => (a 0, a ((0 : Fin 3) + 1)) = pr),
            c6mass (fun i => P i) a))
      = pathDiag (L (iv jx 0)) (w (iv jx 0)) (σ 0) (σ ((0 : Fin 3) + 1)) ^ 10 *
        pathOff (L (iv jx 0)) (w (iv jx 0)) (σ 0) (σ ((0 : Fin 3) + 1)) ^ 6 := by
    rw [Finset.prod_congr rfl (fun pr _ => by rw [c6mass_pair0 _ hti htn pr])]
    exact prod_pair_base _ _ _ _ 10 6
  have hedge1 : (∏ pr : Fin 3 × Fin 3,
        (pathN (L (iv jx 1)) (w (iv jx 1)) (σ 1 pr.1) (σ ((1 : Fin 3) + 1) pr.2)) ^
          (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => (a 1, a ((1 : Fin 3) + 1)) = pr),
            c6mass (fun i => P i) a))
      = pathDiag (L (iv jx 1)) (w (iv jx 1)) (σ 1) (σ ((1 : Fin 3) + 1)) ^ 10 *
        pathOff (L (iv jx 1)) (w (iv jx 1)) (σ 1) (σ ((1 : Fin 3) + 1)) ^ 6 := by
    rw [Finset.prod_congr rfl (fun pr _ => by rw [c6mass_pair1 _ hti htn pr])]
    exact prod_pair_base _ _ _ _ 10 6
  have hedge2 : (∏ pr : Fin 3 × Fin 3,
        (pathN (L (iv jx 2)) (w (iv jx 2)) (σ 2 pr.1) (σ ((2 : Fin 3) + 1) pr.2)) ^
          (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => (a 2, a ((2 : Fin 3) + 1)) = pr),
            c6mass (fun i => P i) a))
      = pathDiag (L (iv jx 2)) (w (iv jx 2)) (σ 2) (fun q => σ 0 (P q)) ^ 10 *
        pathOff (L (iv jx 2)) (w (iv jx 2)) (σ 2) (fun q => σ 0 (P q)) ^ 6 := by
    rw [Finset.prod_congr rfl (fun pr _ => by rw [c6mass_pair2 _ hti htn pr]), he20]
    exact prod_pair_close _ _ _ _ P 10 6
  -- the master mass-weighted bound
  have hmaster : (∏ v, W v) ^ 66 * (∏ g : Fin 3 → Fin 3,
        c6mass (fun i => P i) g ^ c6mass (fun i => P i) g)
      ≤ ∏ g : Fin 3 → Fin 3,
          ((∏ i, w (tv jx i) (σ i (g i))) *
            ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))))
          ^ c6mass (fun i => P i) g := by
    have hsplit : (∏ g : Fin 3 → Fin 3,
          ((∏ i, w (tv jx i) (σ i (g i))) *
            ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))))
            ^ c6mass (fun i => P i) g)
        = (∏ g : Fin 3 → Fin 3,
              (∏ i, w (tv jx i) (σ i (g i))) ^ c6mass (fun i => P i) g) *
          (∏ g : Fin 3 → Fin 3,
              (∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))))
                ^ c6mass (fun i => P i) g) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun g _ => mul_pow _ _ _
    rw [hsplit,
      terminal_exponent_gen (c6mass (fun i => P i)) 22 hUmarg (fun i c => w (tv jx i) (σ i c)),
      pair_exponent_gen (c6mass (fun i => P i))
        (fun i p q => pathN (L (iv jx i)) (w (iv jx i)) (σ i p) (σ (i + 1) q))]
    -- the terminal half
    have hterm : (∏ i : Fin 3, W (tv jx i)) ^ 66
        ≤ ∏ i : Fin 3, ∏ c : Fin 3, w (tv jx i) (σ i c) ^ 22 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_le_prod' fun i _ => ?_
      have h1 : ∏ c ∈ L (tv jx i), w (tv jx i) c = ∏ c : Fin 3, w (tv jx i) (σ i c) :=
        prod_list_eq_prod_index' (hL _) (hmem i) (hinj i) _
      calc W (tv jx i) ^ 66 = (W (tv jx i) ^ 3) ^ 22 := by ring
        _ ≤ (∏ c ∈ L (tv jx i), w (tv jx i) c) ^ 22 := Nat.pow_le_pow_left (hdom _) _
        _ = (∏ c : Fin 3, w (tv jx i) (σ i c)) ^ 22 := by rw [h1]
        _ = ∏ c : Fin 3, w (tv jx i) (σ i c) ^ 22 := (Finset.prod_pow _ _ _).symm
    -- the internal half: two plain cone points and one strict one
    have hint : 2 ^ 60 * 3 ^ 30 * (∏ i : Fin 3, W (iv jx i)) ^ 66
        ≤ 2 ^ 10 * ∏ i : Fin 3, ∏ pr : Fin 3 × Fin 3,
            (pathN (L (iv jx i)) (w (iv jx i)) (σ i pr.1) (σ (i + 1) pr.2)) ^
              (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => (a i, a (i + 1)) = pr),
                c6mass (fun i => P i) a) := by
      rw [Fin.prod_univ_three (fun i : Fin 3 => ∏ pr : Fin 3 × Fin 3,
            (pathN (L (iv jx i)) (w (iv jx i)) (σ i pr.1) (σ (i + 1) pr.2)) ^
              (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => (a i, a (i + 1)) = pr),
                c6mass (fun i => P i) a)),
        hedge0, hedge1, hedge2,
        Fin.prod_univ_three (fun i : Fin 3 => W (iv jx i))]
      have hb0 := hns 0 (σ ((0 : Fin 3) + 1)) pp0
      have hb1 := hns 1 (σ ((1 : Fin 3) + 1)) pp1
      have hb2 := hns 2 (fun q => σ 0 (P q)) pp2
      rcases c6_unequal σ P (hinj 0) hP with hne | hne | hne
      · have hs0 := hst 0 (σ ((0 : Fin 3) + 1)) pp0 (by rwa [he01])
        calc 2 ^ 60 * 3 ^ 30 * (W (iv jx 0) * W (iv jx 1) * W (iv jx 2)) ^ 66
            = 2 ^ 60 * 3 ^ 30 *
                (W (iv jx 1) ^ 66 * W (iv jx 2) ^ 66 * W (iv jx 0) ^ 66) := by ring
          _ ≤ 2 ^ 10 * ((pathDiag (L (iv jx 1)) (w (iv jx 1)) (σ 1) (σ ((1 : Fin 3) + 1)) ^ 10 *
                  pathOff (L (iv jx 1)) (w (iv jx 1)) (σ 1) (σ ((1 : Fin 3) + 1)) ^ 6) *
                (pathDiag (L (iv jx 2)) (w (iv jx 2)) (σ 2) (fun q => σ 0 (P q)) ^ 10 *
                  pathOff (L (iv jx 2)) (w (iv jx 2)) (σ 2) (fun q => σ 0 (P q)) ^ 6) *
                (pathDiag (L (iv jx 0)) (w (iv jx 0)) (σ 0) (σ ((0 : Fin 3) + 1)) ^ 10 *
                  pathOff (L (iv jx 0)) (w (iv jx 0)) (σ 0) (σ ((0 : Fin 3) + 1)) ^ 6)) :=
              c6_three_edges hb1 hb2 hs0
          _ = _ := by ring
      · have hs1 := hst 1 (σ ((1 : Fin 3) + 1)) pp1 (by rwa [he12])
        calc 2 ^ 60 * 3 ^ 30 * (W (iv jx 0) * W (iv jx 1) * W (iv jx 2)) ^ 66
            = 2 ^ 60 * 3 ^ 30 *
                (W (iv jx 0) ^ 66 * W (iv jx 2) ^ 66 * W (iv jx 1) ^ 66) := by ring
          _ ≤ 2 ^ 10 * ((pathDiag (L (iv jx 0)) (w (iv jx 0)) (σ 0) (σ ((0 : Fin 3) + 1)) ^ 10 *
                  pathOff (L (iv jx 0)) (w (iv jx 0)) (σ 0) (σ ((0 : Fin 3) + 1)) ^ 6) *
                (pathDiag (L (iv jx 2)) (w (iv jx 2)) (σ 2) (fun q => σ 0 (P q)) ^ 10 *
                  pathOff (L (iv jx 2)) (w (iv jx 2)) (σ 2) (fun q => σ 0 (P q)) ^ 6) *
                (pathDiag (L (iv jx 1)) (w (iv jx 1)) (σ 1) (σ ((1 : Fin 3) + 1)) ^ 10 *
                  pathOff (L (iv jx 1)) (w (iv jx 1)) (σ 1) (σ ((1 : Fin 3) + 1)) ^ 6)) :=
              c6_three_edges hb0 hb2 hs1
          _ = _ := by ring
      · have hs2 := hst 2 (fun q => σ 0 (P q)) pp2 hne
        calc 2 ^ 60 * 3 ^ 30 * (W (iv jx 0) * W (iv jx 1) * W (iv jx 2)) ^ 66
            = 2 ^ 60 * 3 ^ 30 *
                (W (iv jx 0) ^ 66 * W (iv jx 1) ^ 66 * W (iv jx 2) ^ 66) := by ring
          _ ≤ 2 ^ 10 * ((pathDiag (L (iv jx 0)) (w (iv jx 0)) (σ 0) (σ ((0 : Fin 3) + 1)) ^ 10 *
                  pathOff (L (iv jx 0)) (w (iv jx 0)) (σ 0) (σ ((0 : Fin 3) + 1)) ^ 6) *
                (pathDiag (L (iv jx 1)) (w (iv jx 1)) (σ 1) (σ ((1 : Fin 3) + 1)) ^ 10 *
                  pathOff (L (iv jx 1)) (w (iv jx 1)) (σ 1) (σ ((1 : Fin 3) + 1)) ^ 6) *
                (pathDiag (L (iv jx 2)) (w (iv jx 2)) (σ 2) (fun q => σ 0 (P q)) ^ 10 *
                  pathOff (L (iv jx 2)) (w (iv jx 2)) (σ 2) (fun q => σ 0 (P q)) ^ 6)) :=
              c6_three_edges hb0 hb1 hs2
          _ = _ := by ring
    -- the split of the weight normalizers over the two bipartition classes
    have hWsplit : (∏ v, W v) = (∏ i : Fin 3, W (tv jx i)) * (∏ i : Fin 3, W (iv jx i)) := by
      rw [← Equiv.prod_comp jx (fun v => W v), Fintype.prod_sum_type]
      rfl
    have hent := c6mass_entropy (fun i => P i) hti htn
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 2 ^ 10 by norm_num)
    calc 2 ^ 10 * ((∏ v, W v) ^ 66 * ∏ g : Fin 3 → Fin 3,
            c6mass (fun i => P i) g ^ c6mass (fun i => P i) g)
        ≤ 2 ^ 10 * ((∏ v, W v) ^ 66 * (2 ^ 50 * 3 ^ 30)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hent)
      _ = (∏ i : Fin 3, W (tv jx i)) ^ 66 *
            (2 ^ 60 * 3 ^ 30 * (∏ i : Fin 3, W (iv jx i)) ^ 66) := by
          rw [hWsplit, mul_pow]; ring
      _ ≤ (∏ i : Fin 3, ∏ c : Fin 3, w (tv jx i) (σ i c) ^ 22) *
            (2 ^ 10 * ∏ i : Fin 3, ∏ pr : Fin 3 × Fin 3,
              (pathN (L (iv jx i)) (w (iv jx i)) (σ i pr.1) (σ (i + 1) pr.2)) ^
                (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => (a i, a (i + 1)) = pr),
                  c6mass (fun i => P i) a)) := Nat.mul_le_mul hterm hint
      _ = 2 ^ 10 * ((∏ i : Fin 3, ∏ c : Fin 3, w (tv jx i) (σ i c) ^ 22) *
            ∏ i : Fin 3, ∏ pr : Fin 3 × Fin 3,
              (pathN (L (iv jx i)) (w (iv jx i)) (σ i pr.1) (σ (i + 1) pr.2)) ^
                (∑ a ∈ univ.filter (fun a : Fin 3 → Fin 3 => (a i, a (i + 1)) = pr),
                  c6mass (fun i => P i) a)) := by ring
  -- the three-fibre AM–GM, and the cancellation
  have hfib := fibre_amgm_gen (c6mass (fun i => P i)) 22 (by norm_num) (fun c => hUmarg 0 c) hUpos
    (fun g => (∏ i, w (tv jx i) (σ i (g i))) *
      ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))))
  have hUprodpos : 0 < ∏ g : Fin 3 → Fin 3,
      c6mass (fun i => P i) g ^ c6mass (fun i => P i) g :=
    Finset.prod_pos fun g _ => Nat.pow_pos (hUpos g)
  have hchainA : ((22 * ∏ v, W v) ^ 3) ^ 22 *
        (∏ g : Fin 3 → Fin 3, c6mass (fun i => P i) g ^ c6mass (fun i => P i) g)
      ≤ (∏ c : Fin 3, ∑ g ∈ (univ : Finset (Fin 3 → Fin 3)).filter (fun g => g 0 = c),
            ((∏ i, w (tv jx i) (σ i (g i))) *
              ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))))) ^ 22 *
        (∏ g : Fin 3 → Fin 3, c6mass (fun i => P i) g ^ c6mass (fun i => P i) g) := by
    calc ((22 * ∏ v, W v) ^ 3) ^ 22 *
          (∏ g : Fin 3 → Fin 3, c6mass (fun i => P i) g ^ c6mass (fun i => P i) g)
        = 22 ^ (3 * 22) * ((∏ v, W v) ^ 66 *
            ∏ g : Fin 3 → Fin 3, c6mass (fun i => P i) g ^ c6mass (fun i => P i) g) := by
          rw [← pow_mul, mul_pow]; ring
      _ ≤ 22 ^ (3 * 22) * ∏ g : Fin 3 → Fin 3,
            ((∏ i, w (tv jx i) (σ i (g i))) *
              ∏ i, pathN (L (iv jx i)) (w (iv jx i)) (σ i (g i)) (σ (i + 1) (g (i + 1))))
            ^ c6mass (fun i => P i) g := Nat.mul_le_mul_left _ hmaster
      _ ≤ _ := hfib
  have hcancel := Nat.le_of_mul_le_mul_right hchainA hUprodpos
  rw [hprod]
  exact (Nat.pow_le_pow_iff_left (by norm_num : (22 : ℕ) ≠ 0)).mp hcancel

end Core

end ListColoring

namespace ListColoring

open Finset SimpleGraph RefTensor

section Branch

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem uniformA_three_six : uniformA 3 6 = 22 := by
  simp [uniformA, beta_succ, alpha_succ]

/-- **UM-096 — the `C₆` branch of `cycle_gm_bound_even`**, in exactly the shape
`cycle_gm_bound_even_of_branches` consumes. -/
theorem branch_six : EvenCycleBranchSix V G := by
  intro ix hadj L hL w W hdom
  obtain ⟨jx, hjx, hroot⟩ := exists_cyc_model (M := 2) ix hadj
  obtain ⟨σ, P, hmem, hinj, hchain, hclose⟩ := exists_terminal_closing_model jx L hL
  have hlast : (Fin.last 2 : Fin 3) = 2 := by decide
  by_cases hP : P = 1
  · subst hP
    exact cycle_gm_bound_even_identity (M := 2) (by omega) ix hadj L hL w W hdom jx hjx hroot σ
      hmem hinj hchain (fun x y h => by simpa using hclose x y h)
  · have hA : rootedCol G (constList V 3) (ix 0) 0 = 22 := by
      rw [rootedCol_constList_cycle (by omega : 1 ≤ 3) ix hadj]
      exact uniformA_three_six
    rw [hA, ← hroot]
    exact c6_core jx hjx L hL w W hdom σ P hmem hinj hchain
      (fun x y h => hclose x y (by rw [hlast]; exact h)) hP

end Branch

end ListColoring

namespace ListColoring
open Finset SimpleGraph


/-! ## Axiom audit and the plug into the repository's case split -/

section Audit
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

open ListColoring

/-- `branch_six` is exactly the hypothesis `h5` of `cycle_gm_bound_even_of_branches`. -/
example (h7 : EvenCycleBranchLarge V G) {m : ℕ} (hm : 2 ≤ m) (ix : Fin (m + 1) ≃ V)
    (hadj : ∀ i j : Fin (m + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (hpar : Even (m + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) :
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3 ≤
      ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c :=
  cycle_gm_bound_even_of_branches branch_six h7 hm ix hadj hpar L hL w W hdom

end Audit

end ListColoring

#print axioms ListColoring.c6mass_entropy
#print axioms ListColoring.c6_edge_strict
#print axioms ListColoring.c6_core
#print axioms ListColoring.branch_six


/-! ## Sanity checks on the UM-096 mass tables (no proof depends on these). -/
section Sanity
open ListColoring Finset

/-- the five nontrivial holonomies of `Fin 3`, as plain functions. -/
private def ts : List (Fin 3 → Fin 3) :=
  [![1,0,2], ![0,2,1], ![2,1,0], ![1,2,0], ![2,0,1]]

-- total mass `P = 66` at every holonomy
#guard ts.all fun t => (∑ g : Fin 3 → Fin 3, c6mass t g) == 66

-- every one-coordinate marginal is `E = 22`
#guard ts.all fun t => [0,1,2].all fun i => [0,1,2].all fun c =>
  (∑ g ∈ univ.filter (fun g : Fin 3 → Fin 3 => g i = c), c6mass t g) == 22

-- the three pair marginals are the `(10,6)` base composed with the holonomy
#guard ts.all fun t => [0,1,2].all fun p => [0,1,2].all fun q =>
  ((∑ g ∈ univ.filter (fun g : Fin 3 → Fin 3 => (g 0, g 1) = (p,q)), c6mass t g)
      == (if p = q then 10 else 6)) &&
  ((∑ g ∈ univ.filter (fun g : Fin 3 → Fin 3 => (g 1, g 2) = (p,q)), c6mass t g)
      == (if p = q then 10 else 6)) &&
  ((∑ g ∈ univ.filter (fun g : Fin 3 → Fin 3 => (g 2, g 0) = (p,q)), c6mass t g)
      == (if q = t p then 10 else 6))

-- the entropy denominator is `2^58·3^24` at a transposition and `2^68·3^18` at a three-cycle,
-- and the budget `2^50·3^30` clears both (margins 1.51 and 1.02 bits)
#guard ts.all fun t =>
  decide (∏ g : Fin 3 → Fin 3, c6mass t g ^ c6mass t g < 2 ^ 50 * 3 ^ 30)
#guard ((2 ^ 58 * 3 ^ 24 : ℕ) < 2 ^ 50 * 3 ^ 30) && ((2 ^ 68 * 3 ^ 18 : ℕ) < 2 ^ 50 * 3 ^ 30)

-- the root normalizer of `C₆` is `E = 22`: the branch statement is not the vacuous `0 ≤ _`
#guard uniformA 3 6 == 22

end Sanity
