/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Three

/-!
# The four-cycle case of the even tensor capacity

The first instance of `cycle_gm_bound_even` (UM-104) to fall: `C₄`, i.e. `m = 3`. It carries the
crux cone point `path_cone_four_one` — the `(M,S) = (4,1)` inequality
`2^12 · (∏ x)^6 ≤ pathDiag^4 · pathOff`, which is verbatim the hypothesis `h1` of the existing
`path_cone_two_one_of` and was the one genuinely missing ingredient of the identity-holonomy
branch. `cycle_gm_bound_even_at_three` then discharges the sorried statement at `m = 3`.
-/


namespace ListColoring

open Finset SimpleGraph

section FourOne

variable {Z : Finset ℕ} {x : ℕ → ℕ} {a b : Fin 3 → ℕ}

/-- Two distinct available colours bound `pathN` from below. -/
theorem pair_le_pathN {u v k l : ℕ} (hk : k ∈ Z) (hl : l ∈ Z) (hkl : k ≠ l)
    (hku : k ≠ u) (hkv : k ≠ v) (hlu : l ≠ u) (hlv : l ≠ v) :
    x k + x l ≤ pathN Z x u v := by
  have hsub : ({k, l} : Finset ℕ) ⊆ (Z.erase u).erase v := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_erase.mpr ⟨hkv, Finset.mem_erase.mpr ⟨hku, hk⟩⟩
    · rw [Finset.mem_singleton] at hz
      subst hz
      exact Finset.mem_erase.mpr ⟨hlv, Finset.mem_erase.mpr ⟨hlu, hl⟩⟩
  have hh := Finset.sum_le_sum_of_subset (f := x) hsub
  rw [Finset.sum_insert (by simpa using hkl), Finset.sum_singleton] at hh
  exact hh

/-- Three distinct available colours bound `pathN` from below. -/
theorem triple_le_pathN {u v k l n : ℕ} (hk : k ∈ Z) (hl : l ∈ Z) (hn : n ∈ Z)
    (hkl : k ≠ l) (hkn : k ≠ n) (hln : l ≠ n)
    (hku : k ≠ u) (hkv : k ≠ v) (hlu : l ≠ u) (hlv : l ≠ v) (hnu : n ≠ u) (hnv : n ≠ v) :
    x k + x l + x n ≤ pathN Z x u v := by
  have hsub : ({k, l, n} : Finset ℕ) ⊆ (Z.erase u).erase v := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_erase.mpr ⟨hkv, Finset.mem_erase.mpr ⟨hku, hk⟩⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_erase.mpr ⟨hlv, Finset.mem_erase.mpr ⟨hlu, hl⟩⟩
    · rw [Finset.mem_singleton] at hz
      subst hz
      exact Finset.mem_erase.mpr ⟨hnv, Finset.mem_erase.mpr ⟨hnu, hn⟩⟩
  have hh := Finset.sum_le_sum_of_subset (f := x) hsub
  rw [Finset.sum_insert (by simp [hkl, hkn]), Finset.sum_insert (by simp [hln]),
    Finset.sum_singleton, ← add_assoc] at hh
  exact hh

/-- The polynomial core of the `(4,1)` cone point. -/
theorem four_one_poly (p q r : ℕ) :
    2 ^ 12 * (p * q * r) ^ 6 ≤
      (r * (p + q) * (p + q + r)) ^ 4 * (q * (q + r) * p * (p + q) * (p + r) * (p + q)) := by
  have h1 : 4 * (p * q) ≤ (p + q) ^ 2 := by
    have := amgm_two p q; simpa using this
  have h2 : 4 * (r * (p + q)) ≤ (p + q + r) ^ 2 := by
    have := amgm_two r (p + q)
    calc 4 * (r * (p + q)) = 2 ^ 2 * (r * (p + q)) := by norm_num
      _ ≤ (r + (p + q)) ^ 2 := this
      _ = (p + q + r) ^ 2 := by ring
  have h3 : 8 * (p * q * r) ≤ (q + r) * (p + r) * (p + q) := gm_bridge p q r
  -- k1 : (p+q)^4 ≥ 16 p^2 q^2
  have k1 : 16 * (p ^ 2 * q ^ 2) ≤ (p + q) ^ 4 := by
    have := Nat.pow_le_pow_left h1 2
    calc 16 * (p ^ 2 * q ^ 2) = (4 * (p * q)) ^ 2 := by ring
      _ ≤ ((p + q) ^ 2) ^ 2 := this
      _ = (p + q) ^ 4 := by ring
  -- k2 : (p+q+r)^4 ≥ 16 p q r (p+q)
  have k2 : 16 * (p * q * r * (p + q)) ≤ (p + q + r) ^ 4 := by
    have hpq : 4 * (p * q) ≤ (p + q + r) ^ 2 :=
      le_trans h1 (Nat.pow_le_pow_left (by omega) 2)
    calc 16 * (p * q * r * (p + q)) = (4 * (r * (p + q))) * (4 * (p * q)) := by ring
      _ ≤ (p + q + r) ^ 2 * (p + q + r) ^ 2 := Nat.mul_le_mul h2 hpq
      _ = (p + q + r) ^ 4 := by ring
  -- k3 : (p+q)^2 (p+r)(q+r) ≥ 8 p q r (p+q)
  have k3 : 8 * (p * q * r) * (p + q) ≤ (p + q) ^ 2 * ((p + r) * (q + r)) := by
    calc 8 * (p * q * r) * (p + q) ≤ ((q + r) * (p + r) * (p + q)) * (p + q) :=
          Nat.mul_le_mul_right _ h3
      _ = (p + q) ^ 2 * ((p + r) * (q + r)) := by ring
  have step1 : 2 ^ 12 * (p * q * r) ^ 6 ≤ 2048 * (p ^ 5 * q ^ 5 * r ^ 6) * (p + q) ^ 2 := by
    calc 2 ^ 12 * (p * q * r) ^ 6 = 1024 * (p ^ 5 * q ^ 5 * r ^ 6) * (4 * (p * q)) := by ring
      _ ≤ 1024 * (p ^ 5 * q ^ 5 * r ^ 6) * (p + q) ^ 2 := Nat.mul_le_mul_left _ h1
      _ ≤ 2048 * (p ^ 5 * q ^ 5 * r ^ 6) * (p + q) ^ 2 := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  calc 2 ^ 12 * (p * q * r) ^ 6 ≤ 2048 * (p ^ 5 * q ^ 5 * r ^ 6) * (p + q) ^ 2 := step1
    _ = (p * q) * r ^ 4 * (16 * (p ^ 2 * q ^ 2)) * (8 * (p * q * r) * (p + q)) *
          (16 * (p * q * r * (p + q))) := by ring
    _ ≤ (p * q) * r ^ 4 * ((p + q) ^ 4) * ((p + q) ^ 2 * ((p + r) * (q + r))) *
          ((p + q + r) ^ 4) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ k1) k3) k2
    _ = (r * (p + q) * (p + q + r)) ^ 4 * (q * (q + r) * p * (p + q) * (p + r) * (p + q)) := by
        ring

/-- The assembly of the `(4,1)` certificate from the nine cell bounds. -/
theorem four_one_assemble {p q r d0 d1 d2 e1 e2 e3 e4 e5 e6 : ℕ}
    (hd0 : r ≤ d0) (hd1 : p + q ≤ d1) (hd2 : p + q + r ≤ d2)
    (he1 : q ≤ e1) (he2 : q + r ≤ e2) (he3 : p ≤ e3) (he4 : p + q ≤ e4)
    (he5 : p + r ≤ e5) (he6 : p + q ≤ e6) :
    2 ^ 12 * (p * q * r) ^ 6 ≤ (d0 * d1 * d2) ^ 4 * (e1 * e2 * (e3 * e4) * (e5 * e6)) := by
  calc 2 ^ 12 * (p * q * r) ^ 6
      ≤ (r * (p + q) * (p + q + r)) ^ 4 * (q * (q + r) * p * (p + q) * (p + r) * (p + q)) :=
        four_one_poly p q r
    _ = (r * (p + q) * (p + q + r)) ^ 4 * (q * (q + r) * (p * (p + q)) * ((p + r) * (p + q))) := by
        ring
    _ ≤ (d0 * d1 * d2) ^ 4 * (e1 * e2 * (e3 * e4) * (e5 * e6)) := by
        refine Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.mul_le_mul hd0 hd1) hd2) 4)
          (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul he1 he2) (Nat.mul_le_mul he3 he4))
            (Nat.mul_le_mul he5 he6))

end FourOne

section FourOneCore

variable {Z : Finset ℕ} {x : ℕ → ℕ} {a b : Fin 3 → ℕ}

/-- In a path pattern, the third colour of `Z` beyond a mismatched cell `i`. -/
theorem exists_third {i : Fin 3} (h : IsPathPattern Z a b)
    (hai : a i ∈ Z) (hbi : b i ∈ Z) (hne : a i ≠ b i) :
    ∃ c, c ∈ Z ∧ c ≠ a i ∧ c ≠ b i ∧ Z = {a i, b i, c} ∧
      ∀ z ∈ Z, z ≠ a i → z ≠ b i → z = c := by
  classical
  have hqmem : b i ∈ Z.erase (a i) := Finset.mem_erase.mpr ⟨Ne.symm hne, hbi⟩
  have hcard1 : ((Z.erase (a i)).erase (b i)).card = 1 := by
    rw [Finset.card_erase_of_mem hqmem, Finset.card_erase_of_mem hai, h.cardZ]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
  have hcmem : c ∈ (Z.erase (a i)).erase (b i) := by rw [hc]; exact Finset.mem_singleton_self c
  have hcZ : c ∈ Z := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcmem)
  have hcb : c ≠ b i := Finset.ne_of_mem_erase hcmem
  have hca : c ≠ a i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hcmem)
  refine ⟨c, hcZ, hca, hcb, ?_, ?_⟩
  · have hh : Z.erase (a i) = insert (b i) {c} := by rw [← hc, Finset.insert_erase hqmem]
    rw [← Finset.insert_erase hai, hh]
  · intro z hz hza hzb
    have : z ∈ (Z.erase (a i)).erase (b i) :=
      Finset.mem_erase.mpr ⟨hzb, Finset.mem_erase.mpr ⟨hza, hz⟩⟩
    rw [hc, Finset.mem_singleton] at this
    exact this

/-- Case B of the `(4,1)` cone point, with the mismatched cell at `i` and a cell `n` whose two
colours both avoid `Z`. -/
theorem four_one_caseB (h : IsPathPattern Z a b) (x : ℕ → ℕ) (i m n : Fin 3)
    (him : i ≠ m) (hin : i ≠ n) (hmn : m ≠ n)
    (hai : a i ∈ Z) (hbi : b i ∈ Z) (hne : a i ≠ b i)
    (han : a n ∉ Z) (hbn : b n ∉ Z) :
    2 ^ 12 * (∏ z ∈ Z, x z) ^ 6 ≤
      (pathN Z x (a i) (b i) * pathN Z x (a m) (b m) * pathN Z x (a n) (b n)) ^ 4 *
        (pathN Z x (a i) (b m) * pathN Z x (a i) (b n) *
          (pathN Z x (a m) (b i) * pathN Z x (a m) (b n)) *
          (pathN Z x (a n) (b i) * pathN Z x (a n) (b m))) := by
  classical
  obtain ⟨c, hcZ, hca, hcb, hZeq, -⟩ := exists_third h hai hbi hne
  -- the product of the weights on `Z`
  have hXeq : ∏ z ∈ Z, x z = x (a i) * x (b i) * x c := by
    rw [hZeq, Finset.prod_insert (by simp [hne, Ne.symm hca]),
      Finset.prod_insert (by simp [Ne.symm hcb]), Finset.prod_singleton]
    ring
  -- separation facts
  have haim : a i ≠ a m := fun hh => him (h.injA hh)
  have hain : a i ≠ a n := fun hh => hin (h.injA hh)
  have hbim : b i ≠ b m := fun hh => him (h.injB hh)
  have hbin : b i ≠ b n := fun hh => hin (h.injB hh)
  have haibm : a i ≠ b m := fun hh => him (h.extEq i m hh)
  have hbiam : b i ≠ a m := fun hh => him (h.extEq m i hh.symm).symm
  have haZ : ∀ {z : ℕ}, z ∈ Z → z ≠ a n := fun hz hh => han (hh ▸ hz)
  have hbZ : ∀ {z : ℕ}, z ∈ Z → z ≠ b n := fun hz hh => hbn (hh ▸ hz)
  -- the nine cell bounds
  have hd0 : x c ≤ pathN Z x (a i) (b i) := single_le_pathN hcZ hca hcb
  have hd1 : x (a i) + x (b i) ≤ pathN Z x (a m) (b m) :=
    pair_le_pathN hai hbi hne haim haibm hbiam hbim
  have hd2 : x (a i) + x (b i) + x c ≤ pathN Z x (a n) (b n) :=
    triple_le_pathN hai hbi hcZ hne (Ne.symm hca) (Ne.symm hcb)
      (haZ hai) (hbZ hai) (haZ hbi) (hbZ hbi) (haZ hcZ) (hbZ hcZ)
  have he1 : x (b i) ≤ pathN Z x (a i) (b m) := single_le_pathN hbi (Ne.symm hne) hbim
  have he2 : x (b i) + x c ≤ pathN Z x (a i) (b n) :=
    pair_le_pathN hbi hcZ (Ne.symm hcb) (Ne.symm hne) (hbZ hbi) hca (hbZ hcZ)
  have he3 : x (a i) ≤ pathN Z x (a m) (b i) := single_le_pathN hai haim hne
  have he4 : x (a i) + x (b i) ≤ pathN Z x (a m) (b n) :=
    pair_le_pathN hai hbi hne haim (hbZ hai) hbiam (hbZ hbi)
  have he5 : x (a i) + x c ≤ pathN Z x (a n) (b i) :=
    pair_le_pathN hai hcZ (Ne.symm hca) (haZ hai) hne (haZ hcZ) hcb
  have he6 : x (a i) + x (b i) ≤ pathN Z x (a n) (b m) :=
    pair_le_pathN hai hbi hne (haZ hai) haibm (haZ hbi) hbim
  rw [hXeq]
  exact four_one_assemble hd0 hd1 hd2 he1 he2 he3 he4 he5 he6

/-- If one cell of a path pattern carries two distinct colours of `Z`, then of the two other
cells at least one carries no colour of `Z` at all. -/
theorem clean_index (h : IsPathPattern Z a b) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hai : a i ∈ Z) (hbi : b i ∈ Z) (hne : a i ≠ b i) :
    (a j ∉ Z ∧ b j ∉ Z) ∨ (a k ∉ Z ∧ b k ∉ Z) := by
  classical
  obtain ⟨c, hcZ, hca, hcb, -, hthird⟩ := exists_third h hai hbi hne
  have hA : ∀ l : Fin 3, l ≠ i → a l ∈ Z → a l = c := by
    intro l hl hmem
    exact hthird _ hmem (fun hh => hl (h.injA hh)) (fun hh => hl (h.extEq l i hh))
  have hB : ∀ l : Fin 3, l ≠ i → b l ∈ Z → b l = c := by
    intro l hl hmem
    exact hthird _ hmem (fun hh => hl (h.extEq i l hh.symm).symm) (fun hh => hl (h.injB hh))
  by_cases haj : a j ∈ Z
  · have hajc : a j = c := hA j (Ne.symm hij) haj
    refine Or.inr ⟨?_, ?_⟩
    · intro hmem
      exact hjk (h.injA ((hajc).trans (hA k (Ne.symm hik) hmem).symm))
    · intro hmem
      exact hjk (h.extEq j k ((hajc).trans (hB k (Ne.symm hik) hmem).symm))
  · by_cases hbj : b j ∈ Z
    · have hbjc : b j = c := hB j (Ne.symm hij) hbj
      refine Or.inr ⟨?_, ?_⟩
      · intro hmem
        exact hjk (h.extEq k j ((hA k (Ne.symm hik) hmem).trans hbjc.symm)).symm
      · intro hmem
        exact hjk (h.injB (hbjc.trans (hB k (Ne.symm hik) hmem).symm))
    · exact Or.inl ⟨haj, hbj⟩

/-- **The `(4,1)` cone point at `k = 3`.**  Sharp at `a = b = Z` with constant weights
(`2 ^ 12 = 4096 = 8 ^ 4 · 1`).  This is the inequality the identity-holonomy branch of the even
cycle needs, and hypothesis `h1` of `path_cone_two_one_of`. -/
theorem path_cone_four_one (h : IsPathPattern Z a b) (x : ℕ → ℕ) :
    2 ^ 12 * (∏ z ∈ Z, x z) ^ 6 ≤ pathDiag Z x a b ^ 4 * pathOff Z x a b := by
  classical
  by_cases hB : ∃ i, a i ∈ Z ∧ b i ∈ Z ∧ a i ≠ b i
  · obtain ⟨i, hai, hbi, hne⟩ := hB
    rw [pathDiag_eq, pathOff_eq]
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
    rcases hi with rfl | rfl | rfl
    · rcases clean_index h 0 1 2 (by decide) (by decide) (by decide) hai hbi hne with
        ⟨hna, hnb⟩ | ⟨hna, hnb⟩
      · exact le_trans (four_one_caseB h x 0 2 1 (by decide) (by decide) (by decide)
          hai hbi hne hna hnb) (le_of_eq (by ring))
      · exact le_trans (four_one_caseB h x 0 1 2 (by decide) (by decide) (by decide)
          hai hbi hne hna hnb) (le_of_eq (by ring))
    · rcases clean_index h 1 0 2 (by decide) (by decide) (by decide) hai hbi hne with
        ⟨hna, hnb⟩ | ⟨hna, hnb⟩
      · exact le_trans (four_one_caseB h x 1 2 0 (by decide) (by decide) (by decide)
          hai hbi hne hna hnb) (le_of_eq (by ring))
      · exact le_trans (four_one_caseB h x 1 0 2 (by decide) (by decide) (by decide)
          hai hbi hne hna hnb) (le_of_eq (by ring))
    · rcases clean_index h 2 0 1 (by decide) (by decide) (by decide) hai hbi hne with
        ⟨hna, hnb⟩ | ⟨hna, hnb⟩
      · exact le_trans (four_one_caseB h x 2 1 0 (by decide) (by decide) (by decide)
          hai hbi hne hna hnb) (le_of_eq (by ring))
      · exact le_trans (four_one_caseB h x 2 0 1 (by decide) (by decide) (by decide)
          hai hbi hne hna hnb) (le_of_eq (by ring))
  · have hA : ∀ i, a i ∉ Z ∨ b i ∉ Z ∨ a i = b i := by
      intro i
      by_cases h1 : a i ∈ Z
      · by_cases h2 : b i ∈ Z
        · exact Or.inr (Or.inr (by by_contra hh; exact hB ⟨i, h1, h2, hh⟩))
        · exact Or.inr (Or.inl h2)
      · exact Or.inl h1
    have hd := eight_mul_prod_le_pathDiag (x := x) h hA
    have hoff := path_ray_off (x := x) h
    calc 2 ^ 12 * (∏ z ∈ Z, x z) ^ 6
        = (8 * ∏ z ∈ Z, x z) ^ 4 * (∏ z ∈ Z, x z) ^ 2 := by ring
      _ ≤ pathDiag Z x a b ^ 4 * pathOff Z x a b :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hd 4) hoff

end FourOneCore

/-! ## The `C₄` base case of `cycle_gm_bound_even` -/

section C4

/-- The identity-holonomy reference masses on `C₄`: `4` on the matched cell of each fibre,
`1` off it.  Row and column sums are `E = 6`, the total is `P = 18`, and `∏ U ^ U = 2 ^ 24`
is an equality against the budget — `C₄` has no slack anywhere. -/
def massC4 (c d : Fin 3) : ℕ := if d = c then 4 else 1

theorem massC4_sum (c : Fin 3) : ∑ d : Fin 3, massC4 c d = 6 := by fin_cases c <;> decide
theorem massC4_pos (c d : Fin 3) : 0 < massC4 c d := by unfold massC4; split <;> norm_num
theorem massC4_entropy (c : Fin 3) : ∏ d : Fin 3, massC4 c d ^ massC4 c d = 256 := by
  fin_cases c <;> decide

theorem prod_pow_mass_pair (f : Fin 3 → Fin 3 → ℕ) :
    ∏ c : Fin 3, ∏ d : Fin 3, (f c d) ^ massC4 c d
      = (f 0 0 * f 1 1 * f 2 2) ^ 4 *
        (f 0 1 * f 0 2 * (f 1 0 * f 1 2) * (f 2 0 * f 2 1)) := by
  simp [Fin.prod_univ_three, massC4]; ring

theorem prod_pow_mass_left (A : Fin 3 → ℕ) :
    ∏ c : Fin 3, ∏ d : Fin 3, (A c) ^ massC4 c d = ∏ c : Fin 3, A c ^ 6 := by
  simp [Fin.prod_univ_three, massC4]; ring

theorem prod_pow_mass_right (B : Fin 3 → ℕ) :
    ∏ c : Fin 3, ∏ d : Fin 3, (B d) ^ massC4 c d = ∏ d : Fin 3, B d ^ 6 := by
  simp [Fin.prod_univ_three, massC4]; ring

theorem prod_pow_split (A B : Fin 3 → ℕ) (P Q : Fin 3 → Fin 3 → ℕ) :
    ∏ c : Fin 3, ∏ d : Fin 3, (A c * B d * (P c d * Q c d)) ^ massC4 c d
      = (∏ c : Fin 3, ∏ d : Fin 3, (A c) ^ massC4 c d) *
        ((∏ c : Fin 3, ∏ d : Fin 3, (B d) ^ massC4 c d) *
          ((∏ c : Fin 3, ∏ d : Fin 3, (P c d) ^ massC4 c d) *
            (∏ c : Fin 3, ∏ d : Fin 3, (Q c d) ^ massC4 c d))) := by
  simp only [mul_pow, Finset.prod_mul_distrib]; ring

/-- The fibre AM–GM of `C₄`: `E ^ E ∏ X ^ U ≤ (∑ X) ^ E ∏ U ^ U` with `E = 6`, `∏ U ^ U = 256`. -/
theorem fibre_amgm_c4 (Y : Fin 3 → Fin 3 → ℕ) (c : Fin 3) :
    6 ^ 6 * ∏ d : Fin 3, (Y c d) ^ massC4 c d ≤ (∑ d : Fin 3, Y c d) ^ 6 * 256 := by
  have h := weighted_amgm_masses (univ : Finset (Fin 3)) (Y c) (massC4 c)
    (by norm_num) (massC4_sum c) (fun d _ => massC4_pos c d)
  rw [massC4_entropy c] at h
  exact h

/-- **The `C₄` capacity, in pure arithmetic**: the four vertices pay for the reference masses
(`256 ^ 3 = 2 ^ 24`), the fibre AM–GM converts that into the rooted product. -/
theorem c4_core (A0 A1 : Fin 3 → ℕ) (P0 P1 : Fin 3 → Fin 3 → ℕ) (R : Fin 3 → ℕ)
    (WT0 WT1 WI0 WI1 : ℕ)
    (hR : ∀ c, R c = ∑ d : Fin 3, A0 c * A1 d * (P0 c d * P1 c d))
    (hb0 : WT0 ^ 18 ≤ ∏ c : Fin 3, A0 c ^ 6)
    (hb1 : WT1 ^ 18 ≤ ∏ d : Fin 3, A1 d ^ 6)
    (hi0 : 2 ^ 12 * WI0 ^ 18 ≤ (P0 0 0 * P0 1 1 * P0 2 2) ^ 4 *
        (P0 0 1 * P0 0 2 * (P0 1 0 * P0 1 2) * (P0 2 0 * P0 2 1)))
    (hi1 : 2 ^ 12 * WI1 ^ 18 ≤ (P1 0 0 * P1 1 1 * P1 2 2) ^ 4 *
        (P1 0 1 * P1 0 2 * (P1 1 0 * P1 1 2) * (P1 2 0 * P1 2 1))) :
    (6 * (WT0 * WT1 * (WI0 * WI1))) ^ 3 ≤ ∏ c : Fin 3, R c := by
  classical
  set Y : Fin 3 → Fin 3 → ℕ := fun c d => A0 c * A1 d * (P0 c d * P1 c d) with hY
  have hmaster : 256 ^ 3 * (WT0 * WT1 * (WI0 * WI1)) ^ 18
      ≤ ∏ c : Fin 3, ∏ d : Fin 3, (Y c d) ^ massC4 c d := by
    rw [hY, prod_pow_split, prod_pow_mass_left, prod_pow_mass_right, prod_pow_mass_pair,
      prod_pow_mass_pair]
    calc 256 ^ 3 * (WT0 * WT1 * (WI0 * WI1)) ^ 18
        = WT0 ^ 18 * (WT1 ^ 18 * ((2 ^ 12 * WI0 ^ 18) * (2 ^ 12 * WI1 ^ 18))) := by ring
      _ ≤ (∏ c : Fin 3, A0 c ^ 6) * ((∏ d : Fin 3, A1 d ^ 6) *
            (((P0 0 0 * P0 1 1 * P0 2 2) ^ 4 *
              (P0 0 1 * P0 0 2 * (P0 1 0 * P0 1 2) * (P0 2 0 * P0 2 1))) *
             ((P1 0 0 * P1 1 1 * P1 2 2) ^ 4 *
              (P1 0 1 * P1 0 2 * (P1 1 0 * P1 1 2) * (P1 2 0 * P1 2 1))))) :=
          Nat.mul_le_mul hb0 (Nat.mul_le_mul hb1 (Nat.mul_le_mul hi0 hi1))
  have hfib : 6 ^ 18 * (∏ c : Fin 3, ∏ d : Fin 3, (Y c d) ^ massC4 c d)
      ≤ (∏ c : Fin 3, R c) ^ 6 * 256 ^ 3 := by
    have f0 := fibre_amgm_c4 Y 0
    have f1 := fibre_amgm_c4 Y 1
    have f2 := fibre_amgm_c4 Y 2
    calc 6 ^ 18 * (∏ c : Fin 3, ∏ d : Fin 3, (Y c d) ^ massC4 c d)
        = (6 ^ 6 * ∏ d : Fin 3, (Y 0 d) ^ massC4 0 d) *
            ((6 ^ 6 * ∏ d : Fin 3, (Y 1 d) ^ massC4 1 d) *
              (6 ^ 6 * ∏ d : Fin 3, (Y 2 d) ^ massC4 2 d)) := by
          rw [Fin.prod_univ_three]; ring
      _ ≤ ((∑ d : Fin 3, Y 0 d) ^ 6 * 256) *
            (((∑ d : Fin 3, Y 1 d) ^ 6 * 256) * ((∑ d : Fin 3, Y 2 d) ^ 6 * 256)) :=
          Nat.mul_le_mul f0 (Nat.mul_le_mul f1 f2)
      _ = (∏ c : Fin 3, R c) ^ 6 * 256 ^ 3 := by
          rw [Fin.prod_univ_three, hR 0, hR 1, hR 2]; ring
  have hkey : ((6 * (WT0 * WT1 * (WI0 * WI1))) ^ 3) ^ 6 * 256 ^ 3
      ≤ (∏ c : Fin 3, R c) ^ 6 * 256 ^ 3 := by
    calc ((6 * (WT0 * WT1 * (WI0 * WI1))) ^ 3) ^ 6 * 256 ^ 3
        = 6 ^ 18 * (256 ^ 3 * (WT0 * WT1 * (WI0 * WI1)) ^ 18) := by ring
      _ ≤ 6 ^ 18 * (∏ c : Fin 3, ∏ d : Fin 3, (Y c d) ^ massC4 c d) :=
          Nat.mul_le_mul_left _ hmaster
      _ ≤ (∏ c : Fin 3, R c) ^ 6 * 256 ^ 3 := hfib
  have h6 := Nat.le_of_mul_le_mul_right hkey (by norm_num : 0 < 256 ^ 3)
  exact (Nat.pow_le_pow_iff_left (by norm_num : (6:ℕ) ≠ 0)).mp h6

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem pathN_symm (Z : Finset ℕ) (x : ℕ → ℕ) (u v : ℕ) : pathN Z x u v = pathN Z x v u := by
  unfold pathN; congr 1; exact Finset.erase_right_comm

theorem sum_filter_fin2 {α : Type*} [AddCommMonoid α] (c : Fin 3) (F : (Fin 2 → Fin 3) → α) :
    ∑ g ∈ (univ : Finset (Fin 2 → Fin 3)).filter (fun g => g 0 = c), F g
      = ∑ d : Fin 3, F ![c, d] := by
  classical
  refine (Finset.sum_nbij' (i := fun d => (![c, d] : Fin 2 → Fin 3)) (j := fun g => g 1)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro d _; simp
  · intro g _; exact Finset.mem_univ _
  · intro d _; simp
  · intro g hg
    rw [Finset.mem_filter] at hg
    funext i
    fin_cases i <;> simp [hg.2]
  · intro d _; rfl

/-- The rooted profile of `C₄` in tensor coordinates: given the two terminal colours the two
internal vertices are independent, so the summand factorises. -/
theorem c4_rootedWcol (jx : CycIx 1 ≃ V)
    (hjx : ∀ x y, G.Adj (jx x) (jx y) ↔ CycAdj x y)
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ)
    (σ : Fin 2 → Fin 3 → ℕ) (hσmem : ∀ i x, σ i x ∈ L (tv jx i))
    (hσinj : ∀ i, Function.Injective (σ i)) (c : Fin 3) :
    rootedWcol G L w (tv jx 0) (σ 0 c)
      = ∑ d : Fin 3, w (tv jx 0) (σ 0 c) * w (tv jx 1) (σ 1 d) *
          (pathN (L (iv jx 0)) (w (iv jx 0)) (σ 0 c) (σ 1 d) *
            pathN (L (iv jx 1)) (w (iv jx 1)) (σ 0 c) (σ 1 d)) := by
  rw [rootedWcol_eq_sum_index jx hjx L hL w σ hσmem hσinj c, sum_filter_fin2]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [show (1 : Fin 2) + 1 = 0 by decide, show (0 : Fin 2) + 1 = 1 by decide,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [pathN_symm (L (iv jx 1)) (w (iv jx 1)) (σ 1 d) (σ 0 c)]

/-- **UM-090: the `C₄` base case of `cycle_gm_bound_even`** (`m = 3`, four vertices).  The
holonomy is forced to be the identity, the reference masses are `4` on the matched cell and `1`
elsewhere, and the whole bound closes with equality at the constant list. -/
theorem cycle_gm_bound_even_four (ix : Fin (3 + 1) ≃ V)
    (hadj : ∀ i j : Fin (3 + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) :
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3 ≤
      ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c := by
  classical
  obtain ⟨jx, hjx, hroot⟩ := exists_cyc_model (M := 1) ix hadj
  obtain ⟨σ, hσmem, hσinj, hσchain⟩ := exists_terminal_enum_chain jx L hL
  -- the uniform normalizer of `C₄` is `A = uniformA 3 4 = 6 = E`
  have hA : rootedCol G (constList V 3) (ix 0) 0 = 6 := by
    rw [rootedCol_constList_cycle (by omega : 1 ≤ 3) ix hadj]
    simp [uniformA, beta_succ, alpha_succ]
  -- the enumeration chain aligns the two terminal lists: the holonomy is the identity
  have hext : ∀ p q : Fin 3, σ 0 p = σ 1 q → p = q := by
    intro p q hpq
    have hmem : σ 0 p ∈ L (tv jx 1) := hpq ▸ hσmem 1 q
    exact hσinj 1 ((hσchain 0 (by decide) p hmem).trans hpq)
  have hpp : ∀ i : Fin 2, IsPathPattern (L (iv jx i)) (σ 0) (σ 1) :=
    fun i => ⟨hL (iv jx i), hσinj 0, hσinj 1, hext⟩
  have hprodW : ∏ v, W v = W (tv jx 0) * W (tv jx 1) * (W (iv jx 0) * W (iv jx 1)) := by
    rw [← Equiv.prod_comp jx (fun v => W v), Fintype.prod_sum_type, Fin.prod_univ_two,
      Fin.prod_univ_two]
    rfl
  have hprodroot : ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c
      = ∏ c : Fin 3, rootedWcol G L w (ix 0) (σ 0 c) := by
    rw [← hroot, ← enum_image (hL (tv jx 0)) (hσmem 0) (hσinj 0),
      Finset.prod_image (fun p _ q _ h => hσinj 0 h)]
  -- the terminal half: `hdom` at the two terminals, no slack
  have hterm : ∀ i : Fin 2, W (tv jx i) ^ 18 ≤ ∏ c : Fin 3, (w (tv jx i) (σ i c)) ^ 6 := by
    intro i
    have himg : ∏ x : Fin 3, w (tv jx i) (σ i x) = ∏ c ∈ L (tv jx i), w (tv jx i) c := by
      rw [← enum_image (hL (tv jx i)) (hσmem i) (hσinj i),
        Finset.prod_image (fun p _ q _ h => hσinj i h)]
    rw [Finset.prod_pow, himg]
    calc W (tv jx i) ^ 18 = (W (tv jx i) ^ 3) ^ 6 := by ring
      _ ≤ (∏ c ∈ L (tv jx i), w (tv jx i) c) ^ 6 := Nat.pow_le_pow_left (hdom _) 6
  -- the internal half: the `(4,1)` cone point at each internal vertex
  have hint : ∀ i : Fin 2, 2 ^ 12 * W (iv jx i) ^ 18 ≤
      (pathN (L (iv jx i)) (w (iv jx i)) (σ 0 0) (σ 1 0) *
        pathN (L (iv jx i)) (w (iv jx i)) (σ 0 1) (σ 1 1) *
        pathN (L (iv jx i)) (w (iv jx i)) (σ 0 2) (σ 1 2)) ^ 4 *
      (pathN (L (iv jx i)) (w (iv jx i)) (σ 0 0) (σ 1 1) *
        pathN (L (iv jx i)) (w (iv jx i)) (σ 0 0) (σ 1 2) *
        (pathN (L (iv jx i)) (w (iv jx i)) (σ 0 1) (σ 1 0) *
          pathN (L (iv jx i)) (w (iv jx i)) (σ 0 1) (σ 1 2)) *
        (pathN (L (iv jx i)) (w (iv jx i)) (σ 0 2) (σ 1 0) *
          pathN (L (iv jx i)) (w (iv jx i)) (σ 0 2) (σ 1 1))) := by
    intro i
    have h := path_cone_four_one (hpp i) (w (iv jx i))
    rw [pathDiag_eq, pathOff_eq] at h
    refine le_trans (Nat.mul_le_mul_left _ ?_) h
    calc W (iv jx i) ^ 18 = (W (iv jx i) ^ 3) ^ 6 := by ring
      _ ≤ (∏ c ∈ L (iv jx i), w (iv jx i) c) ^ 6 := Nat.pow_le_pow_left (hdom _) 6
  rw [hA, hprodW, hprodroot]
  exact c4_core (fun c => w (tv jx 0) (σ 0 c)) (fun d => w (tv jx 1) (σ 1 d))
    (fun c d => pathN (L (iv jx 0)) (w (iv jx 0)) (σ 0 c) (σ 1 d))
    (fun c d => pathN (L (iv jx 1)) (w (iv jx 1)) (σ 0 c) (σ 1 d))
    (fun c => rootedWcol G L w (ix 0) (σ 0 c))
    (W (tv jx 0)) (W (tv jx 1)) (W (iv jx 0)) (W (iv jx 1))
    (fun c => by rw [← hroot]; exact c4_rootedWcol jx hjx L hL w σ hσmem hσinj c)
    (hterm 0) (hterm 1) (hint 0) (hint 1)

/-- The statement of `cycle_gm_bound_even` at `m = 3` is exactly the theorem above. -/
theorem cycle_gm_bound_even_at_three (hm : 2 ≤ 3) (ix : Fin (3 + 1) ≃ V)
    (hadj : ∀ i j : Fin (3 + 1), G.Adj (ix i) (ix j) ↔ (j = i + 1 ∨ i = j + 1))
    (hpar : Even (3 + 1))
    (L : ListAssignment V) (hL : IsNListAssignment L 3) (w : V → ℕ → ℕ) (W : V → ℕ)
    (hdom : ∀ v, (W v) ^ 3 ≤ ∏ c ∈ L v, w v c) :
    (rootedCol G (constList V 3) (ix 0) 0 * ∏ v, W v) ^ 3 ≤
      ∏ c ∈ L (ix 0), rootedWcol G L w (ix 0) c :=
  cycle_gm_bound_even_four ix hadj L hL w W hdom

#print axioms path_cone_four_one
#print axioms cycle_gm_bound_even_four
#print axioms cycle_gm_bound_even_at_three

end C4

/-- The two integer comparisons of the note's own UM-096 budget (`c6_exponent_cone_and_holonomy.md`
§5), stated with the note's constant `R(10,6) = 2^108/(5^10·11^22)`.

Caveat, established while formalising `C₆`: `path_strict_pow` does **not** deliver `R(10,6)` — it
delivers `(729/256)^5 = 3^30/2^40`, which is 1.12 bits weaker. The `C₆` proof in
`Cacti/C6Branch.lean` therefore does not use these; it runs on the budget `2^50·3^30` against the
entropies `2^58·3^24` and `2^68·3^18`, with margins of 1.51 and 1.02 bits. These two comparisons
are kept because they are the note's stated arithmetic, not because the proof needs them. -/
theorem um096_clears_transposition : 3 ^ 24 * 5 ^ 10 * 11 ^ 22 < 2 ^ 140 := by norm_num

theorem um096_clears_three_cycle : 3 ^ 18 * 5 ^ 10 * 11 ^ 22 < 2 ^ 130 := by norm_num

end ListColoring
