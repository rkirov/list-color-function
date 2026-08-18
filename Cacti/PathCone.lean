/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Tensor
import Cacti.Induction
import Mathlib.Combinatorics.Hall.Finite

/-!
# The `k = 3` two-edge three-list path layer (handoff §5.4)
-/

namespace ListColoring

open Finset

/-- `N(a,b) = ∑_{z ∈ Z \ {a,b}} x z`. -/
def pathN (Z : Finset ℕ) (x : ℕ → ℕ) (a b : ℕ) : ℕ := ∑ z ∈ (Z.erase a).erase b, x z

/-- `∏_i N(a i, b i)`. -/
def pathDiag (Z : Finset ℕ) (x : ℕ → ℕ) (a b : Fin 3 → ℕ) : ℕ :=
  ∏ i : Fin 3, pathN Z x (a i) (b i)

/-- `∏_{i ≠ j} N(a i, b j)`. -/
def pathOff (Z : Finset ℕ) (x : ℕ → ℕ) (a b : Fin 3 → ℕ) : ℕ :=
  ∏ i : Fin 3, ∏ j ∈ (univ : Finset (Fin 3)).erase i, pathN Z x (a i) (b j)

structure IsPathPattern (Z : Finset ℕ) (a b : Fin 3 → ℕ) : Prop where
  cardZ : Z.card = 3
  injA : Function.Injective a
  injB : Function.Injective b
  extEq : ∀ i j, a i = b j → i = j

variable {Z : Finset ℕ} {x : ℕ → ℕ} {a b : Fin 3 → ℕ}

/-! ## Basic facts about `pathN` -/

theorem single_le_pathN {u v k : ℕ} (hk : k ∈ Z) (h1 : k ≠ u) (h2 : k ≠ v) :
    x k ≤ pathN Z x u v :=
  Finset.single_le_sum (f := x) (fun _ _ => Nat.zero_le _)
    (by simp [Finset.mem_erase, hk, h1, h2])

/-! ## The routing (SDR) lemma -/

private theorem erase2_subset (Z : Finset ℕ) (u v : ℕ) : (Z.erase u).erase v ⊆ Z :=
  ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))

private theorem card_erase2 (Z : Finset ℕ) (u v : ℕ) :
    Z.card - 2 ≤ ((Z.erase u).erase v).card := by
  have h1 : (Z.erase u).card - 1 ≤ ((Z.erase u).erase v).card := Finset.pred_card_le_card_erase
  have h2 : Z.card - 1 ≤ (Z.erase u).card := Finset.pred_card_le_card_erase
  omega

private theorem mem_erase2 {Z : Finset ℕ} {u v k : ℕ} (hk : k ∈ Z)
    (h : k ∉ (Z.erase u).erase v) : k = u ∨ k = v := by
  simp only [Finset.mem_erase, hk, and_true, not_and_or, not_not] at h
  tauto

/-- If the family `Z \ {u i, v i}` has an SDR then the product of the weights on `Z` is at most
the product of the three path sums. -/
theorem prod_le_prod_pathN (hZ : Z.card = 3) (x : ℕ → ℕ) {u v : Fin 3 → ℕ}
    {f : Fin 3 → ℕ} (hf : Function.Injective f)
    (hmem : ∀ i, f i ∈ (Z.erase (u i)).erase (v i)) :
    ∏ z ∈ Z, x z ≤ ∏ i, pathN Z x (u i) (v i) := by
  classical
  have hsub : (univ : Finset (Fin 3)).image f ⊆ Z := by
    intro k hk
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hk
    obtain ⟨i, rfl⟩ := hk
    exact erase2_subset Z (u i) (v i) (hmem i)
  have hcard : ((univ : Finset (Fin 3)).image f).card = 3 := by
    rw [Finset.card_image_of_injective _ hf]; simp
  have himg : (univ : Finset (Fin 3)).image f = Z :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hZ, hcard])
  calc ∏ z ∈ Z, x z = ∏ z ∈ (univ : Finset (Fin 3)).image f, x z := by rw [himg]
    _ = ∏ i : Fin 3, x (f i) := Finset.prod_image (fun i _ j _ h => hf h)
    _ ≤ ∏ i : Fin 3, pathN Z x (u i) (v i) := by
        refine Finset.prod_le_prod' (fun i _ => ?_)
        have := hmem i
        simp only [Finset.mem_erase] at this
        exact single_le_pathN this.2.2 this.2.1 this.1

/-- Hall's marriage theorem for three sets, with the condition reduced to the three
cardinalities that can fail. -/
theorem exists_inj_mem3 {T : Fin 3 → Finset ℕ}
    (h1 : ∀ i, 1 ≤ (T i).card)
    (h2 : ∀ i j : Fin 3, i ≠ j → 2 ≤ (T i ∪ T j).card)
    (h3 : 3 ≤ ((univ : Finset (Fin 3)).biUnion T).card) :
    ∃ f : Fin 3 → ℕ, Function.Injective f ∧ ∀ i, f i ∈ T i := by
  classical
  refine (Finset.all_card_le_biUnion_card_iff_existsInjective' T).mp ?_
  intro s
  have hs3 : s.card ≤ 3 := by
    have := Finset.card_le_univ s; simpa using this
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 := by omega
  rcases hcases with hsc | hsc | hsc | hsc
  · omega
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hsc
    simpa using h1 i
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hsc
    have hb : ({i, j} : Finset (Fin 3)).biUnion T = T i ∪ T j := by
      simp [Finset.biUnion_insert]
    rw [hb, hsc]
    exact h2 i j hij
  · have hsu : s = univ := Finset.eq_univ_of_card s (by simpa using hsc)
    subst hsu
    rw [hsc]
    exact h3

/-- **The routing lemma.**  Under the two injectivity hypotheses and the "no reversed pair"
hypothesis, the family `Z \ {u i, v i}` has a system of distinct representatives, hence the
product of the three path sums dominates the product of the weights on `Z`. -/
theorem path_route (hZ : Z.card = 3) (x : ℕ → ℕ) {u v : Fin 3 → ℕ}
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hpair : ∀ i j : Fin 3, i ≠ j → ¬ (v i = u j ∧ v j = u i ∧ u i ∈ Z ∧ u j ∈ Z)) :
    ∏ z ∈ Z, x z ≤ ∏ i, pathN Z x (u i) (v i) := by
  classical
  let t : Fin 3 → Finset ℕ := fun i => (Z.erase (u i)).erase (v i)
  have ht : ∀ i, t i = (Z.erase (u i)).erase (v i) := fun _ => rfl
  -- every set has at least one element
  have hone : ∀ i, 1 ≤ (t i).card := by
    intro i
    have h := card_erase2 Z (u i) (v i)
    rw [hZ] at h
    rw [ht i]
    omega
  -- a singleton forces both erased points to lie in `Z`
  have hmemZ : ∀ i, (t i).card = 1 → u i ∈ Z ∧ v i ∈ Z := by
    intro i hi
    rw [ht i] at hi
    by_cases hu' : u i ∈ Z
    · refine ⟨hu', ?_⟩
      by_contra hv'
      have he : (Z.erase (u i)).erase (v i) = Z.erase (u i) :=
        Finset.erase_eq_of_notMem (fun h => hv' (Finset.mem_of_mem_erase h))
      rw [he, Finset.card_erase_of_mem hu', hZ] at hi
      omega
    · exfalso
      have he : Z.erase (u i) = Z := Finset.erase_eq_of_notMem hu'
      have h2 : 2 ≤ (Z.erase (v i)).card := by
        have := Finset.pred_card_le_card_erase (s := Z) (a := v i); omega
      rw [he] at hi; omega
  -- no two of them can be the same singleton
  have hpairun : ∀ i j : Fin 3, i ≠ j → 2 ≤ (t i ∪ t j).card := by
    intro i j hij
    by_contra hc0
    have hc : (t i ∪ t j).card < 2 := by omega
    have hi : t i ⊆ t i ∪ t j := Finset.subset_union_left
    have hj : t j ⊆ t i ∪ t j := Finset.subset_union_right
    have hci : (t i).card = 1 :=
      le_antisymm (le_trans (Finset.card_le_card hi) (by omega)) (hone i)
    have hcj : (t j).card = 1 :=
      le_antisymm (le_trans (Finset.card_le_card hj) (by omega)) (hone j)
    have e1 : t i = t i ∪ t j := Finset.eq_of_subset_of_card_le hi (by omega)
    have e2 : t j = t i ∪ t j := Finset.eq_of_subset_of_card_le hj (by omega)
    have heq : t i = t j := e1.trans e2.symm
    obtain ⟨hui, hvi⟩ := hmemZ i hci
    obtain ⟨huj, hvj⟩ := hmemZ j hcj
    have h1 : u j ∉ t i := by rw [heq, ht j]; simp
    have h2 : v j ∉ t i := by rw [heq, ht j]; simp
    rw [ht i] at h1 h2
    have d1 : u j = u i ∨ u j = v i := mem_erase2 huj h1
    have d2 : v j = u i ∨ v j = v i := mem_erase2 hvj h2
    have hne1 : u j ≠ u i := fun h => hij (hu h).symm
    have hne2 : v j ≠ v i := fun h => hij (hv h).symm
    exact hpair i j hij ⟨(d1.resolve_left hne1).symm, d2.resolve_right hne2, hui, huj⟩
  -- all three together exhaust `Z`
  have hunion3 : 3 ≤ ((univ : Finset (Fin 3)).biUnion t).card := by
    have hsubZ : Z ⊆ (univ : Finset (Fin 3)).biUnion t := by
      intro k hk
      by_contra hc
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at hc
      have e0 := mem_erase2 hk (ht 0 ▸ hc 0)
      have e1 := mem_erase2 hk (ht 1 ▸ hc 1)
      have e2 := mem_erase2 hk (ht 2 ▸ hc 2)
      rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
      · exact absurd (hu (e0 ▸ e1)) (by decide)
      · exact absurd (hu (e0 ▸ e1)) (by decide)
      · exact absurd (hu (e0 ▸ e2)) (by decide)
      · exact absurd (hv (e1 ▸ e2)) (by decide)
      · exact absurd (hu (e1 ▸ e2)) (by decide)
      · exact absurd (hv (e0 ▸ e2)) (by decide)
      · exact absurd (hv (e0 ▸ e1)) (by decide)
      · exact absurd (hv (e0 ▸ e1)) (by decide)
    calc 3 = Z.card := hZ.symm
      _ ≤ _ := Finset.card_le_card hsubZ
  obtain ⟨f, hf, hfm⟩ := exists_inj_mem3 hone hpairun hunion3
  exact prod_le_prod_pathN hZ x hf (fun i => (ht i) ▸ hfm i)

/-- The routing lemma in explicit three-argument form. -/
theorem path_route3 (hZ : Z.card = 3) (x : ℕ → ℕ) (u0 u1 u2 v0 v1 v2 : ℕ)
    (hu01 : u0 ≠ u1) (hu02 : u0 ≠ u2) (hu12 : u1 ≠ u2)
    (hv01 : v0 ≠ v1) (hv02 : v0 ≠ v2) (hv12 : v1 ≠ v2)
    (hp01 : ¬ (v0 = u1 ∧ v1 = u0 ∧ u0 ∈ Z ∧ u1 ∈ Z))
    (hp02 : ¬ (v0 = u2 ∧ v2 = u0 ∧ u0 ∈ Z ∧ u2 ∈ Z))
    (hp12 : ¬ (v1 = u2 ∧ v2 = u1 ∧ u1 ∈ Z ∧ u2 ∈ Z)) :
    ∏ z ∈ Z, x z ≤ pathN Z x u0 v0 * pathN Z x u1 v1 * pathN Z x u2 v2 := by
  have hu : Function.Injective ![u0, u1, u2] := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  have hv : Function.Injective ![v0, v1, v2] := by
    intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  have hp : ∀ i j : Fin 3, i ≠ j →
      ¬ (![v0, v1, v2] i = ![u0, u1, u2] j ∧ ![v0, v1, v2] j = ![u0, u1, u2] i ∧
          ![u0, u1, u2] i ∈ Z ∧ ![u0, u1, u2] j ∈ Z) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> tauto
  have := path_route hZ x hu hv hp
  simpa [Fin.prod_univ_three] using this

/-! ## Expanding the two products -/

theorem pathDiag_eq (Z : Finset ℕ) (x : ℕ → ℕ) (a b : Fin 3 → ℕ) :
    pathDiag Z x a b =
      pathN Z x (a 0) (b 0) * pathN Z x (a 1) (b 1) * pathN Z x (a 2) (b 2) := by
  simp [pathDiag, Fin.prod_univ_three]

theorem pathOff_eq (Z : Finset ℕ) (x : ℕ → ℕ) (a b : Fin 3 → ℕ) :
    pathOff Z x a b =
      pathN Z x (a 0) (b 1) * pathN Z x (a 0) (b 2) *
        (pathN Z x (a 1) (b 0) * pathN Z x (a 1) (b 2)) *
          (pathN Z x (a 2) (b 0) * pathN Z x (a 2) (b 1)) := by
  have e0 : (univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
  have e1 : (univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
  have e2 : (univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
  simp [pathOff, Fin.prod_univ_three, e0, e1, e2]

/-! ## The residual layer -/

/-- The identity system `(a i, b i)` always routes. -/
theorem route_id (h : IsPathPattern Z a b) (x : ℕ → ℕ) :
    ∏ z ∈ Z, x z ≤
      pathN Z x (a 0) (b 0) * pathN Z x (a 1) (b 1) * pathN Z x (a 2) (b 2) := by
  refine path_route3 h.cardZ x _ _ _ _ _ _
    (fun hh => absurd (h.injA hh) (by decide)) (fun hh => absurd (h.injA hh) (by decide))
    (fun hh => absurd (h.injA hh) (by decide)) (fun hh => absurd (h.injB hh) (by decide))
    (fun hh => absurd (h.injB hh) (by decide)) (fun hh => absurd (h.injB hh) (by decide))
    ?_ ?_ ?_
  · exact fun hh => absurd (h.extEq 1 0 hh.1.symm) (by decide)
  · exact fun hh => absurd (h.extEq 2 0 hh.1.symm) (by decide)
  · exact fun hh => absurd (h.extEq 2 1 hh.1.symm) (by decide)

/-- The three-cycle system `(a 0, b 2), (a 1, b 0), (a 2, b 1)` always routes. -/
theorem route_cycle (h : IsPathPattern Z a b) (x : ℕ → ℕ) :
    ∏ z ∈ Z, x z ≤
      pathN Z x (a 0) (b 2) * pathN Z x (a 1) (b 0) * pathN Z x (a 2) (b 1) := by
  refine path_route3 h.cardZ x _ _ _ _ _ _
    (fun hh => absurd (h.injA hh) (by decide)) (fun hh => absurd (h.injA hh) (by decide))
    (fun hh => absurd (h.injA hh) (by decide)) (fun hh => absurd (h.injB hh) (by decide))
    (fun hh => absurd (h.injB hh) (by decide)) (fun hh => absurd (h.injB hh) (by decide))
    ?_ ?_ ?_
  · exact fun hh => absurd (h.extEq 1 2 hh.1.symm) (by decide)
  · exact fun hh => absurd (h.extEq 0 1 hh.2.1.symm) (by decide)
  · exact fun hh => absurd (h.extEq 2 0 hh.1.symm) (by decide)

/-- The other three-cycle system `(a 0, b 1), (a 1, b 2), (a 2, b 0)` always routes. -/
theorem route_cycle' (h : IsPathPattern Z a b) (x : ℕ → ℕ) :
    ∏ z ∈ Z, x z ≤
      pathN Z x (a 0) (b 1) * pathN Z x (a 1) (b 2) * pathN Z x (a 2) (b 0) := by
  refine path_route3 h.cardZ x _ _ _ _ _ _
    (fun hh => absurd (h.injA hh) (by decide)) (fun hh => absurd (h.injA hh) (by decide))
    (fun hh => absurd (h.injA hh) (by decide)) (fun hh => absurd (h.injB hh) (by decide))
    (fun hh => absurd (h.injB hh) (by decide)) (fun hh => absurd (h.injB hh) (by decide))
    ?_ ?_ ?_
  · exact fun hh => absurd (h.extEq 0 2 hh.2.1.symm) (by decide)
  · exact fun hh => absurd (h.extEq 2 1 hh.1.symm) (by decide)
  · exact fun hh => absurd (h.extEq 1 0 hh.2.1.symm) (by decide)

/-- **P2 = UM-092 at `k = 3`**: the off-matching extreme ray `(M,S) = (0,1)`. -/
theorem path_ray_off (h : IsPathPattern Z a b) :
    (∏ z ∈ Z, x z) ^ 2 ≤ pathOff Z x a b := by
  have h1 := route_cycle' h x
  have h2 := route_cycle h x
  calc (∏ z ∈ Z, x z) ^ 2 = (∏ z ∈ Z, x z) * (∏ z ∈ Z, x z) := sq _
    _ ≤ (pathN Z x (a 0) (b 1) * pathN Z x (a 1) (b 2) * pathN Z x (a 2) (b 0)) *
        (pathN Z x (a 0) (b 2) * pathN Z x (a 1) (b 0) * pathN Z x (a 2) (b 1)) :=
          Nat.mul_le_mul h1 h2
    _ = _ := by rw [pathOff_eq]; ring

/-- Three-cycle / ordinary edge, `D = [[1,0,1],[1,1,0],[0,1,1]]`, `d = 2`. -/
theorem path_residual_three_cycle_ordinary (h : IsPathPattern Z a b) :
    (∏ z ∈ Z, x z) ^ 2 ≤
      pathN Z x (a 0) (b 0) * pathN Z x (a 0) (b 2) *
        (pathN Z x (a 1) (b 0) * pathN Z x (a 1) (b 1)) *
          (pathN Z x (a 2) (b 1) * pathN Z x (a 2) (b 2)) := by
  have h1 := route_id h x
  have h2 := route_cycle h x
  calc (∏ z ∈ Z, x z) ^ 2 = (∏ z ∈ Z, x z) * (∏ z ∈ Z, x z) := sq _
    _ ≤ (pathN Z x (a 0) (b 0) * pathN Z x (a 1) (b 1) * pathN Z x (a 2) (b 2)) *
        (pathN Z x (a 0) (b 2) * pathN Z x (a 1) (b 0) * pathN Z x (a 2) (b 1)) :=
          Nat.mul_le_mul h1 h2
    _ = _ := by ring

/-- Three-cycle / closing edge, `D = [[0,0,2],[2,0,0],[0,2,0]]`, `d = 2`, stated halved. -/
theorem path_residual_three_cycle_closing (h : IsPathPattern Z a b) :
    ∏ z ∈ Z, x z ≤
      pathN Z x (a 0) (b 2) * pathN Z x (a 1) (b 0) * pathN Z x (a 2) (b 1) :=
  route_cycle h x

/-- Transposition / ordinary edge, `D = [[1,1,0],[1,1,0],[0,0,2]]`, `d = 2`. -/
theorem path_residual_trans_ordinary (h : IsPathPattern Z a b) :
    (∏ z ∈ Z, x z) ^ 2 ≤
      pathN Z x (a 0) (b 0) * pathN Z x (a 0) (b 1) *
        (pathN Z x (a 1) (b 0) * pathN Z x (a 1) (b 1)) * pathN Z x (a 2) (b 2) ^ 2 := by
  classical
  have hid := route_id h x
  by_cases hfail : a 0 = b 0 ∧ a 1 = b 1 ∧ a 0 ∈ Z ∧ a 1 ∈ Z
  · -- the seam configuration: route by hand
    obtain ⟨hb0, hb1, hp, hq⟩ := hfail
    have hpq : a 0 ≠ a 1 := fun hh => absurd (h.injA hh) (by decide)
    have hqmem : a 1 ∈ Z.erase (a 0) := Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩
    have hcard1 : ((Z.erase (a 0)).erase (a 1)).card = 1 := by
      rw [Finset.card_erase_of_mem hqmem, Finset.card_erase_of_mem hp, h.cardZ]
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
    have hwmem : w ∈ (Z.erase (a 0)).erase (a 1) := by
      rw [hw]; exact Finset.mem_singleton_self w
    have hwZ : w ∈ Z := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hwmem)
    have hwq : w ≠ a 1 := Finset.ne_of_mem_erase hwmem
    have hwp : w ≠ a 0 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hwmem)
    have hZeq : Z = insert (a 0) (insert (a 1) {w}) := by
      have e1 : Z.erase (a 0) = insert (a 1) {w} := by
        rw [← hw, Finset.insert_erase hqmem]
      rw [← Finset.insert_erase hp, e1]
    have hXeq : ∏ z ∈ Z, x z = x (a 0) * (x (a 1) * x w) := by
      rw [hZeq, Finset.prod_insert (by simp [hpq, Ne.symm hwp]),
        Finset.prod_insert (by simp [Ne.symm hwq]), Finset.prod_singleton]
    -- the six bounds
    have b1 : x (a 1) ≤ pathN Z x (a 0) (b 0) := by
      rw [← hb0]; exact single_le_pathN hq (Ne.symm hpq) (Ne.symm hpq)
    have b2 : x w ≤ pathN Z x (a 0) (b 1) := by
      rw [← hb1]; exact single_le_pathN hwZ hwp hwq
    have b3 : x w ≤ pathN Z x (a 1) (b 0) := by
      rw [← hb0]; exact single_le_pathN hwZ hwq hwp
    have b4 : x (a 0) ≤ pathN Z x (a 1) (b 1) := by
      rw [← hb1]; exact single_le_pathN hp hpq hpq
    have hb02 : a 0 ≠ b 2 := fun hh =>
      absurd (h.injB (show b 0 = b 2 from hb0.symm.trans hh)) (by decide)
    have hb12 : a 1 ≠ b 2 := fun hh =>
      absurd (h.injB (show b 1 = b 2 from hb1.symm.trans hh)) (by decide)
    have b5 : x (a 0) ≤ pathN Z x (a 2) (b 2) :=
      single_le_pathN hp (fun hh => absurd (h.injA hh) (by decide)) hb02
    have b6 : x (a 1) ≤ pathN Z x (a 2) (b 2) :=
      single_le_pathN hq (fun hh => absurd (h.injA hh) (by decide)) hb12
    have b56 : x (a 0) * x (a 1) ≤ pathN Z x (a 2) (b 2) ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul b5 b6
    calc (∏ z ∈ Z, x z) ^ 2
        = x (a 1) * x w * (x w * x (a 0)) * (x (a 0) * x (a 1)) := by rw [hXeq]; ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul b1 b2) (Nat.mul_le_mul b3 b4)) b56
  · -- the generic case: the transposition system routes
    have hswap : ∏ z ∈ Z, x z ≤
        pathN Z x (a 0) (b 1) * pathN Z x (a 1) (b 0) * pathN Z x (a 2) (b 2) := by
      refine path_route3 h.cardZ x _ _ _ _ _ _
        (fun hh => absurd (h.injA hh) (by decide)) (fun hh => absurd (h.injA hh) (by decide))
        (fun hh => absurd (h.injA hh) (by decide)) (fun hh => absurd (h.injB hh) (by decide))
        (fun hh => absurd (h.injB hh) (by decide)) (fun hh => absurd (h.injB hh) (by decide))
        ?_ ?_ ?_
      · exact fun hh => hfail ⟨hh.2.1.symm, hh.1.symm, hh.2.2.1, hh.2.2.2⟩
      · exact fun hh => absurd (h.extEq 2 1 hh.1.symm) (by decide)
      · exact fun hh => absurd (h.extEq 2 0 hh.1.symm) (by decide)
    calc (∏ z ∈ Z, x z) ^ 2 = (∏ z ∈ Z, x z) * (∏ z ∈ Z, x z) := sq _
      _ ≤ (pathN Z x (a 0) (b 0) * pathN Z x (a 1) (b 1) * pathN Z x (a 2) (b 2)) *
          (pathN Z x (a 0) (b 1) * pathN Z x (a 1) (b 0) * pathN Z x (a 2) (b 2)) :=
            Nat.mul_le_mul hid hswap
      _ = _ := by ring

/-- Transposition / closing edge, `D = [[2,2,0],[2,2,0],[0,0,4]]`, `d = 4`: the square. -/
theorem path_residual_trans_closing (h : IsPathPattern Z a b) :
    (∏ z ∈ Z, x z) ^ 4 ≤
      (pathN Z x (a 0) (b 0) * pathN Z x (a 0) (b 1) *
        (pathN Z x (a 1) (b 0) * pathN Z x (a 1) (b 1)) * pathN Z x (a 2) (b 2) ^ 2) ^ 2 := by
  have hh := path_residual_trans_ordinary (x := x) h
  calc (∏ z ∈ Z, x z) ^ 4 = ((∏ z ∈ Z, x z) ^ 2) ^ 2 := by ring
    _ ≤ _ := Nat.pow_le_pow_left hh 2

/-! ## The scalar algebra of the cone -/

/-- Uniform AM–GM on a pair. -/
theorem amgm_two (u v : ℕ) : 2 ^ 2 * (u * v) ≤ (u + v) ^ 2 := by
  zify
  nlinarith [sq_nonneg ((u : ℤ) - v)]

/-- Uniform AM–GM on a triple, from `card_pow_mul_prod_le_sum_pow_nat`. -/
theorem amgm_three (u v w : ℕ) : 3 ^ 3 * (u * v * w) ≤ (u + v + w) ^ 3 := by
  have hh := card_pow_mul_prod_le_sum_pow_nat ({0, 1, 2} : Finset ℕ)
    (fun i => if i = 0 then u else if i = 1 then v else w)
  simp [Finset.sum_insert, Finset.prod_insert, Finset.mem_insert] at hh
  convert hh using 2 <;> ring

/-- `P2'` is the `ℕ`-square-root of `P1 · P2`. -/
theorem path_cone_two_one_of {D O X : ℕ}
    (h1 : 2 ^ 12 * X ^ 6 ≤ D ^ 4 * O) (h2 : X ^ 2 ≤ O) :
    2 ^ 6 * X ^ 4 ≤ D ^ 2 * O := by
  refine (Nat.pow_le_pow_iff_left (two_ne_zero)).mp ?_
  calc (2 ^ 6 * X ^ 4) ^ 2 = (2 ^ 12 * X ^ 6) * X ^ 2 := by ring
    _ ≤ (D ^ 4 * O) * O := Nat.mul_le_mul h1 h2
    _ = (D ^ 2 * O) ^ 2 := by ring

/-- Non-strict cone point `(M,S) = (2n, n+s)`. -/
theorem path_cone_pow {D O X : ℕ}
    (h2' : 2 ^ 6 * X ^ 4 ≤ D ^ 2 * O) (h2 : X ^ 2 ≤ O) (n s : ℕ) :
    2 ^ (6 * n) * X ^ (4 * n + 2 * s) ≤ (D ^ 2 * O) ^ n * O ^ s := by
  have hn : (2 ^ 6 * X ^ 4) ^ n ≤ (D ^ 2 * O) ^ n := Nat.pow_le_pow_left h2' n
  have hs : (X ^ 2) ^ s ≤ O ^ s := Nat.pow_le_pow_left h2 s
  calc 2 ^ (6 * n) * X ^ (4 * n + 2 * s)
      = (2 ^ 6 * X ^ 4) ^ n * (X ^ 2) ^ s := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, pow_add]; ring
    _ ≤ (D ^ 2 * O) ^ n * O ^ s := Nat.mul_le_mul hn hs

/-- Strict cone point `(M,S) = (2n, n+s)` on an unequal-list path. -/
theorem path_strict_pow {D O X : ℕ}
    (h3 : 729 * X ^ 4 ≤ 4 * (D ^ 2 * O)) (h2 : X ^ 2 ≤ O) (n s : ℕ) :
    729 ^ n * X ^ (4 * n + 2 * s) ≤ 4 ^ n * ((D ^ 2 * O) ^ n * O ^ s) := by
  have hn : (729 * X ^ 4) ^ n ≤ (4 * (D ^ 2 * O)) ^ n := Nat.pow_le_pow_left h3 n
  have hs : (X ^ 2) ^ s ≤ O ^ s := Nat.pow_le_pow_left h2 s
  calc 729 ^ n * X ^ (4 * n + 2 * s)
      = (729 * X ^ 4) ^ n * (X ^ 2) ^ s := by
        rw [mul_pow, ← pow_mul, ← pow_mul, pow_add]; ring
    _ ≤ (4 * (D ^ 2 * O)) ^ n * O ^ s := Nat.mul_le_mul hn hs
    _ = 4 ^ n * ((D ^ 2 * O) ^ n * O ^ s) := by rw [mul_pow]; ring


/-! ## The interior cone point `(M,S) = (2,1)` (P2') -/

/-- **Case A of P2'**: when no index carries two *different* colours of `Z` at its two ends, the
diagonal alone clears the bridge factor `8`, by `gm_bridge_prod`. -/
theorem eight_mul_prod_le_pathDiag (h : IsPathPattern Z a b)
    (hA : ∀ i, a i ∉ Z ∨ b i ∉ Z ∨ a i = b i) :
    8 * ∏ z ∈ Z, x z ≤ pathDiag Z x a b := by
  classical
  obtain ⟨e, hev⟩ : ∃ e : Fin 3 → ℕ, ∀ i, e i = if a i ∈ Z then a i else b i :=
    ⟨_, fun _ => rfl⟩
  have hsub : ∀ i, Z.erase (e i) ⊆ (Z.erase (a i)).erase (b i) := by
    intro i z hz
    rw [Finset.mem_erase] at hz
    obtain ⟨hzne, hzZ⟩ := hz
    by_cases hai : a i ∈ Z
    · rw [hev i, if_pos hai] at hzne
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨hzne, hzZ⟩⟩
      intro hzb
      have hbi : b i ∈ Z := hzb ▸ hzZ
      rcases hA i with hh | hh | hh
      · exact hh hai
      · exact hh hbi
      · exact hzne (hzb.trans hh.symm)
    · rw [hev i, if_neg hai] at hzne
      exact Finset.mem_erase.mpr ⟨hzne, Finset.mem_erase.mpr ⟨fun hh => hai (hh ▸ hzZ), hzZ⟩⟩
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
  have hkey : ∀ i, Z.erase (ψ i) ⊆ (Z.erase (a i)).erase (b i) := by
    intro i
    by_cases hi : e i ∈ Z
    · have hpsi : ψ i = e i := by
        have hm := hψmem i
        rw [hTv i, if_pos hi] at hm
        simpa using hm
      rw [hpsi]; exact hsub i
    · have hai : a i ∉ Z := by
        intro hh
        exact hi (by rw [hev i, if_pos hh]; exact hh)
      have hbi : b i ∉ Z := by
        intro hh
        exact hi (by rw [hev i, if_neg hai]; exact hh)
      intro z hz
      have hzZ : z ∈ Z := Finset.mem_of_mem_erase hz
      exact Finset.mem_erase.mpr ⟨fun hh => hbi (hh ▸ hzZ),
        Finset.mem_erase.mpr ⟨fun hh => hai (hh ▸ hzZ), hzZ⟩⟩
  have himg : (univ : Finset (Fin 3)).image ψ = Z := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro z hz
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
      obtain ⟨i, rfl⟩ := hz
      exact hψZ i
    · rw [Finset.card_image_of_injective _ hψinj, h.cardZ]; simp
  calc 8 * ∏ z ∈ Z, x z ≤ ∏ z ∈ Z, ∑ d ∈ Z.erase z, x d := gm_bridge_prod h.cardZ x
    _ = ∏ i : Fin 3, ∑ d ∈ Z.erase (ψ i), x d := by
        rw [← himg, Finset.prod_image (fun i _ j _ hh => hψinj hh)]
    _ ≤ ∏ i : Fin 3, pathN Z x (a i) (b i) :=
        Finset.prod_le_prod' (fun i _ => Finset.sum_le_sum_of_subset (hkey i))
    _ = pathDiag Z x a b := rfl

/-- Two cells both carrying the colour `A`, at least one of them also carrying `C`. -/
theorem pathN_pair_bound {p q r s A C : ℕ} (hA : A ∈ Z) (hC : C ∈ Z)
    (hAp : A ≠ p) (hAq : A ≠ q) (hAr : A ≠ r) (hAs : A ≠ s)
    (hC2 : (C ≠ p ∧ C ≠ q) ∨ (C ≠ r ∧ C ≠ s)) :
    x A * x C ≤ pathN Z x p q * pathN Z x r s := by
  rcases hC2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · calc x A * x C = x C * x A := by ring
      _ ≤ pathN Z x p q * pathN Z x r s :=
          Nat.mul_le_mul (single_le_pathN hC h1 h2) (single_le_pathN hA hAr hAs)
  · exact Nat.mul_le_mul (single_le_pathN hA hAp hAq) (single_le_pathN hC h1 h2)

/-- The arithmetic of the `Case B` certificate: two `4`s from the AM–GM pairs and one from the
seam pair make `64`. -/
theorem p2p_assemble {A B C d0 d1 d2 e0 e1 f0 f1 g0 g1 : ℕ}
    (h0 : C ≤ d0) (h1 : A + B ≤ d1) (h2 : A + B ≤ d2)
    (h3 : A + B ≤ e0) (h4 : A + B ≤ e1)
    (h5 : B * C ≤ f0 * f1) (h6 : A * C ≤ g0 * g1) :
    64 * (A * B * C) ^ 4 ≤ (d0 * d1 * d2) ^ 2 * (e0 * e1 * (f0 * f1) * (g0 * g1)) := by
  have hsq : 4 * (A * B) ≤ (A + B) * (A + B) := by
    have := amgm_two A B; nlinarith [this]
  have hab : 4 * (A * B) ≤ d1 * d2 := le_trans hsq (Nat.mul_le_mul h1 h2)
  have hab' : 4 * (A * B) ≤ e0 * e1 := le_trans hsq (Nat.mul_le_mul h3 h4)
  have hd : C ^ 2 * (4 * (A * B)) ^ 2 ≤ (d0 * d1 * d2) ^ 2 := by
    have hstep : C * (4 * (A * B)) ≤ d0 * (d1 * d2) := Nat.mul_le_mul h0 hab
    calc C ^ 2 * (4 * (A * B)) ^ 2 = (C * (4 * (A * B))) ^ 2 := by ring
      _ ≤ (d0 * (d1 * d2)) ^ 2 := Nat.pow_le_pow_left hstep 2
      _ = (d0 * d1 * d2) ^ 2 := by ring
  have ho : 4 * (A * B) * (B * C) * (A * C) ≤ e0 * e1 * (f0 * f1) * (g0 * g1) :=
    Nat.mul_le_mul (Nat.mul_le_mul hab' h5) h6
  calc 64 * (A * B * C) ^ 4
      = C ^ 2 * (4 * (A * B)) ^ 2 * (4 * (A * B) * (B * C) * (A * C)) := by ring
    _ ≤ _ := Nat.mul_le_mul hd ho

/-- **P2' = UM-093 at `k = 3`, `(M,S) = (2,1)`**: the only interior cone point the even-cycle
proof consumes.  Sharp at `A = B = Z`, `x ≡ 1` (`64 = 64`). -/
theorem path_cone_two_one (h : IsPathPattern Z a b) :
    2 ^ 6 * (∏ z ∈ Z, x z) ^ 4 ≤ pathDiag Z x a b ^ 2 * pathOff Z x a b := by
  classical
  by_cases hB : ∃ i, a i ∈ Z ∧ b i ∈ Z ∧ a i ≠ b i
  · obtain ⟨i, hai, hbi, hne⟩ := hB
    have hqmem : b i ∈ Z.erase (a i) := Finset.mem_erase.mpr ⟨Ne.symm hne, hbi⟩
    have hcard1 : ((Z.erase (a i)).erase (b i)).card = 1 := by
      rw [Finset.card_erase_of_mem hqmem, Finset.card_erase_of_mem hai, h.cardZ]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
    have hcmem : c ∈ (Z.erase (a i)).erase (b i) := by
      rw [hc]; exact Finset.mem_singleton_self c
    have hcZ : c ∈ Z := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hcmem)
    have hcb : c ≠ b i := Finset.ne_of_mem_erase hcmem
    have hca : c ≠ a i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hcmem)
    have hZeq : Z = insert (a i) (insert (b i) {c}) := by
      have hh : Z.erase (a i) = insert (b i) {c} := by rw [← hc, Finset.insert_erase hqmem]
      rw [← Finset.insert_erase hai, hh]
    have hXeq : ∏ z ∈ Z, x z = x (a i) * x (b i) * x c := by
      rw [hZeq, Finset.prod_insert (by simp [hne, Ne.symm hca]),
        Finset.prod_insert (by simp [Ne.symm hcb]), Finset.prod_singleton]
      ring
    have hab : ∀ j, a i ≠ b j := by
      intro j hh
      have hij : i = j := h.extEq i j hh
      subst hij
      exact hne hh
    have hba : ∀ j, b i ≠ a j := by
      intro j hh
      have hji : j = i := h.extEq j i hh.symm
      subst hji
      exact hne hh.symm
    have hfour : ∀ p q : Fin 3, p ≠ i → q ≠ i →
        x (a i) + x (b i) ≤ pathN Z x (a p) (b q) := by
      intro p q hp hq
      have hmem1 : a i ∈ (Z.erase (a p)).erase (b q) := by
        simp only [Finset.mem_erase]
        exact ⟨hab q, fun hh => hp (h.injA hh).symm, hai⟩
      have hmem2 : b i ∈ (Z.erase (a p)).erase (b q) := by
        simp only [Finset.mem_erase]
        exact ⟨fun hh => hq (h.injB hh).symm, hba p, hbi⟩
      show x (a i) + x (b i) ≤ ∑ z ∈ (Z.erase (a p)).erase (b q), x z
      calc x (a i) + x (b i) = ∑ z ∈ ({a i, b i} : Finset ℕ), x z := by
            rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
        _ ≤ _ := Finset.sum_le_sum_of_subset (by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact hmem1
            · exact hmem2)
    have hrow : ∀ q r : Fin 3, q ≠ i → r ≠ i → q ≠ r →
        x (b i) * x c ≤ pathN Z x (a i) (b q) * pathN Z x (a i) (b r) := by
      intro q r hq hr hqr
      refine pathN_pair_bound hbi hcZ (hba i) (fun hh => hq (h.injB hh).symm) (hba i)
        (fun hh => hr (h.injB hh).symm) ?_
      by_cases hcq : c = b q
      · exact Or.inr ⟨hca, fun hh => hqr (h.injB (hcq.symm.trans hh))⟩
      · exact Or.inl ⟨hca, hcq⟩
    have hcol : ∀ q r : Fin 3, q ≠ i → r ≠ i → q ≠ r →
        x (a i) * x c ≤ pathN Z x (a q) (b i) * pathN Z x (a r) (b i) := by
      intro q r hq hr hqr
      refine pathN_pair_bound hai hcZ (fun hh => hq (h.injA hh).symm) (hab i)
        (fun hh => hr (h.injA hh).symm) (hab i) ?_
      by_cases hcq : c = a q
      · exact Or.inr ⟨fun hh => hqr (h.injA (hcq.symm.trans hh)), hcb⟩
      · exact Or.inl ⟨hcq, hcb⟩
    have hdiag : x c ≤ pathN Z x (a i) (b i) := single_le_pathN hcZ hca hcb
    rw [pathDiag_eq, pathOff_eq, hXeq]
    fin_cases i
    · calc (2:ℕ) ^ 6 * (x (a 0) * x (b 0) * x c) ^ 4
          = 64 * (x (a 0) * x (b 0) * x c) ^ 4 := by norm_num
        _ ≤ (pathN Z x (a 0) (b 0) * pathN Z x (a 1) (b 1) * pathN Z x (a 2) (b 2)) ^ 2 *
            (pathN Z x (a 1) (b 2) * pathN Z x (a 2) (b 1) *
              (pathN Z x (a 0) (b 1) * pathN Z x (a 0) (b 2)) *
              (pathN Z x (a 1) (b 0) * pathN Z x (a 2) (b 0))) :=
            p2p_assemble hdiag (hfour 1 1 (by decide) (by decide))
              (hfour 2 2 (by decide) (by decide)) (hfour 1 2 (by decide) (by decide))
              (hfour 2 1 (by decide) (by decide)) (hrow 1 2 (by decide) (by decide) (by decide))
              (hcol 1 2 (by decide) (by decide) (by decide))
        _ = _ := by ring
    · calc (2:ℕ) ^ 6 * (x (a 1) * x (b 1) * x c) ^ 4
          = 64 * (x (a 1) * x (b 1) * x c) ^ 4 := by norm_num
        _ ≤ (pathN Z x (a 1) (b 1) * pathN Z x (a 0) (b 0) * pathN Z x (a 2) (b 2)) ^ 2 *
            (pathN Z x (a 0) (b 2) * pathN Z x (a 2) (b 0) *
              (pathN Z x (a 1) (b 0) * pathN Z x (a 1) (b 2)) *
              (pathN Z x (a 0) (b 1) * pathN Z x (a 2) (b 1))) :=
            p2p_assemble hdiag (hfour 0 0 (by decide) (by decide))
              (hfour 2 2 (by decide) (by decide)) (hfour 0 2 (by decide) (by decide))
              (hfour 2 0 (by decide) (by decide)) (hrow 0 2 (by decide) (by decide) (by decide))
              (hcol 0 2 (by decide) (by decide) (by decide))
        _ = _ := by ring
    · calc (2:ℕ) ^ 6 * (x (a 2) * x (b 2) * x c) ^ 4
          = 64 * (x (a 2) * x (b 2) * x c) ^ 4 := by norm_num
        _ ≤ (pathN Z x (a 2) (b 2) * pathN Z x (a 0) (b 0) * pathN Z x (a 1) (b 1)) ^ 2 *
            (pathN Z x (a 0) (b 1) * pathN Z x (a 1) (b 0) *
              (pathN Z x (a 2) (b 0) * pathN Z x (a 2) (b 1)) *
              (pathN Z x (a 0) (b 2) * pathN Z x (a 1) (b 2))) :=
            p2p_assemble hdiag (hfour 0 0 (by decide) (by decide))
              (hfour 1 1 (by decide) (by decide)) (hfour 0 1 (by decide) (by decide))
              (hfour 1 0 (by decide) (by decide)) (hrow 0 1 (by decide) (by decide) (by decide))
              (hcol 0 1 (by decide) (by decide) (by decide))
        _ = _ := by ring
  · have hA : ∀ i, a i ∉ Z ∨ b i ∉ Z ∨ a i = b i := by
      intro i
      by_cases h1 : a i ∈ Z
      · by_cases h2 : b i ∈ Z
        · refine Or.inr (Or.inr ?_)
          by_contra hh
          exact hB ⟨i, h1, h2, hh⟩
        · exact Or.inr (Or.inl h2)
      · exact Or.inl h1
    have hd := eight_mul_prod_le_pathDiag (x := x) h hA
    have hoff := path_ray_off (x := x) h
    calc 2 ^ 6 * (∏ z ∈ Z, x z) ^ 4
        = (8 * ∏ z ∈ Z, x z) ^ 2 * (∏ z ∈ Z, x z) ^ 2 := by ring
      _ ≤ pathDiag Z x a b ^ 2 * pathOff Z x a b :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hd 2) hoff

end ListColoring
