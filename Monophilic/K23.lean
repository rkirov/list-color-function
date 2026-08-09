/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fin.VecNotation

/-!
# Lemma 6 of Kirov–Naimi: `K₂,₃` is 2-monophilic

Kirov–Naimi single out `K₂,₃` (Lemma 6) as a base case in their analysis of the 2-monophilic
graphs. We model it as Mathlib's `completeBipartiteGraph (Fin 2) (Fin 3)`, a graph on
`Fin 2 ⊕ Fin 3`.

## The counting reduction

The two left vertices are non-adjacent to each other, the three right vertices are pairwise
non-adjacent, and every left vertex is adjacent to every right vertex. So a coloring from `L` is
built by choosing colors `a ∈ L (inl 0)` and `b ∈ L (inl 1)` freely and then, independently for
each right vertex, any color of its list other than `a` and `b`:

`col (K₂,₃, L) = ∑ a ∈ L (inl 0), ∑ b ∈ L (inl 1), ∏ j, #(L (inr j) \ {a, b})`.

This is `SimpleGraph.col_completeBipartite_two_three`, and it reduces Lemma 6 to the finite
combinatorial statement `SimpleGraph.two_le_sum_prod_sdiff_pair` about five two-element sets.

## Main results

* `SimpleGraph.col_completeBipartite_two_three` : the product formula above
* `SimpleGraph.colConst_completeBipartite_two_three_two` : `col(K₂,₃, 2) = 2`
* `SimpleGraph.two_le_sum_prod_sdiff_pair` : the combinatorial core, `2 ≤ ∑∑∏`
* `SimpleGraph.monophilic_K23` : **Lemma 6**, `K₂,₃` is 2-monophilic
-/

open Finset

namespace SimpleGraph

/-- Adjacency in a complete bipartite graph is decidable: it is a disjunction of `Bool` equalities.
-/
instance instDecidableRelCompleteBipartiteGraphAdj (V W : Type*) :
    DecidableRel (completeBipartiteGraph V W).Adj :=
  fun v w => inferInstanceAs (Decidable (v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft))

/-! ### Adjacency in a complete bipartite graph -/

section Adj

variable {V W : Type*}

@[simp] lemma completeBipartiteGraph_adj_inl_inr (v : V) (w : W) :
    (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inr w) := Or.inl ⟨rfl, rfl⟩

@[simp] lemma completeBipartiteGraph_adj_inr_inl (w : W) (v : V) :
    (completeBipartiteGraph V W).Adj (Sum.inr w) (Sum.inl v) := Or.inr ⟨rfl, rfl⟩

@[simp] lemma completeBipartiteGraph_not_adj_inl_inl (v v' : V) :
    ¬ (completeBipartiteGraph V W).Adj (Sum.inl v) (Sum.inl v') := by
  rintro (⟨-, h⟩ | ⟨h, -⟩) <;> exact Bool.noConfusion h

@[simp] lemma completeBipartiteGraph_not_adj_inr_inr (w w' : W) :
    ¬ (completeBipartiteGraph V W).Adj (Sum.inr w) (Sum.inr w') := by
  rintro (⟨h, -⟩ | ⟨-, h⟩) <;> exact Bool.noConfusion h

/-- A coloring of a complete bipartite graph is proper exactly when no color is used on both
sides. -/
lemma isProperColoring_completeBipartiteGraph_iff {f : V ⊕ W → ℕ} :
    (completeBipartiteGraph V W).IsProperColoring f ↔ ∀ v w, f (Sum.inl v) ≠ f (Sum.inr w) := by
  refine ⟨fun h v w => h (completeBipartiteGraph_adj_inl_inr v w), fun h => ?_⟩
  rintro (v | w) (v' | w') hadj
  · exact absurd hadj (completeBipartiteGraph_not_adj_inl_inl v v')
  · exact h v w'
  · exact fun hc => h v' w hc.symm
  · exact absurd hadj (completeBipartiteGraph_not_adj_inr_inr w w')

end Adj

/-! ### The product formula for `K₂,₃` -/

section Formula

variable {L : ListAssignment (Fin 2 ⊕ Fin 3)} {a b : ℕ}

/-- The colorings of `K₂,₃` from `L` that give the color `a` to `inl 0` and the color `b` to
`inl 1` are exactly the choices, for each right vertex `j`, of a color in
`L (inr j) \ {a, b}`. -/
private lemma card_filter_completeBipartite_two_three
    (ha : a ∈ L (Sum.inl 0)) (hb : b ∈ L (Sum.inl 1)) :
    (((completeBipartiteGraph (Fin 2) (Fin 3)).colorings L).filter
        fun f => (f (Sum.inl 0), f (Sum.inl 1)) = (a, b)).card
      = ∏ j : Fin 3, (L (Sum.inr j) \ {a, b}).card := by
  rw [← Fintype.card_piFinset]
  refine Finset.card_nbij' (fun f j => f (Sum.inr j)) (fun g => Sum.elim ![a, b] g) ?_ ?_ ?_ ?_
  · -- forward: the right-hand colors avoid `a` and `b`
    intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, mem_colorings, Prod.mk.injEq] at hf
    obtain ⟨⟨hmem, hproper⟩, h0, h1⟩ := hf
    rw [isProperColoring_completeBipartiteGraph_iff] at hproper
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact fun j => ⟨hmem _, fun hc => hproper 0 j (h0 ▸ hc.symm),
      fun hc => hproper 1 j (h1 ▸ hc.symm)⟩
  · -- backward: any such choice extends `a, b` to a coloring
    intro g hg
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hg
    simp only [Finset.mem_coe, Finset.mem_filter, mem_colorings, Prod.mk.injEq]
    refine ⟨⟨?_, ?_⟩, rfl, rfl⟩
    · rintro (i | j)
      · fin_cases i
        · exact ha
        · exact hb
      · exact (hg j).1
    · rw [isProperColoring_completeBipartiteGraph_iff]
      intro i j
      fin_cases i
      · exact fun hc => (hg j).2.1 hc.symm
      · exact fun hc => (hg j).2.2 hc.symm
  · -- the two maps are mutually inverse
    intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Prod.mk.injEq] at hf
    funext v
    rcases v with i | j
    · fin_cases i
      · exact hf.2.1.symm
      · exact hf.2.2.symm
    · rfl
  · intro g _; funext j; rfl

variable (L)

/-- **The product formula for `K₂,₃`.** A coloring is a free choice of colors `a`, `b` for the two
left vertices together with, independently for each right vertex, a color of its list avoiding both
`a` and `b`. -/
theorem col_completeBipartite_two_three :
    (completeBipartiteGraph (Fin 2) (Fin 3)).col L
      = ∑ a ∈ L (Sum.inl 0), ∑ b ∈ L (Sum.inl 1),
          ∏ j : Fin 3, (L (Sum.inr j) \ {a, b}).card := by
  have hfib : ∀ f ∈ (completeBipartiteGraph (Fin 2) (Fin 3)).colorings L,
      (f (Sum.inl 0), f (Sum.inl 1)) ∈ L (Sum.inl 0) ×ˢ L (Sum.inl 1) := by
    intro f hf
    exact Finset.mem_product.mpr ⟨mem_list_of_mem_colorings hf _, mem_list_of_mem_colorings hf _⟩
  rw [col, Finset.card_eq_sum_card_fiberwise hfib, Finset.sum_product]
  exact Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb =>
    card_filter_completeBipartite_two_three ha hb

end Formula

/-- `col(K₂,₃, 2) = 2`: from the constant list `{0, 1}` the only colorings are the two that give
one color to the whole left side and the other to the whole right side. -/
theorem colConst_completeBipartite_two_three_two :
    (completeBipartiteGraph (Fin 2) (Fin 3)).colConst 2 = 2 := by decide

/-! ### The combinatorial core

Everything below is about five two-element sets of naturals: `X` and `Y` are the lists of the two
left vertices and `Z 0, Z 1, Z 2` those of the three right vertices. Call a pair `(a, b)` *good*
when no right list equals `{a, b}`; a good pair contributes a nonzero term to the product
formula. -/

section Core

variable {X Y : Finset ℕ} {Z : Fin 3 → Finset ℕ} {a b : ℕ}

/-- A two-element set that is not equal to `{a, b}` is not contained in `{a, b}` either, so it
retains a color after deleting `a` and `b`. -/
private lemma one_le_card_sdiff_pair {s : Finset ℕ} (hs : s.card = 2) (hne : s ≠ {a, b}) :
    1 ≤ (s \ {a, b}).card := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos, Finset.sdiff_nonempty]
  intro hsub
  refine hne (Finset.eq_of_subset_of_card_le hsub ?_)
  rw [hs]
  exact (Finset.card_insert_le _ _).trans (by simp)

/-- A two-element set avoiding both `a` and `b` loses nothing when `a` and `b` are deleted. -/
private lemma two_le_card_sdiff_pair {s : Finset ℕ} (hs : s.card = 2) (ha : a ∉ s) (hb : b ∉ s) :
    2 ≤ (s \ {a, b}).card := by
  have h : s \ {a, b} = s := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, and_iff_left_iff_imp]
    rintro hx (rfl | rfl)
    · exact ha hx
    · exact hb hx
  rw [h, hs]

/-- A two-element set contains an element different from any prescribed one. -/
private lemma exists_mem_ne_of_card_eq_two {s : Finset ℕ} (hs : s.card = 2) (c : ℕ) :
    ∃ u ∈ s, u ≠ c := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
  by_cases h : x = c
  · exact ⟨y, by simp, fun hy => hxy (h.trans hy.symm)⟩
  · exact ⟨x, by simp, h⟩

/-- A good pair contributes a term that is at least `1`. -/
private lemma one_le_prod_sdiff_pair (hZ : ∀ j, (Z j).card = 2) (hgood : ∀ j, Z j ≠ {a, b}) :
    1 ≤ ∏ j : Fin 3, (Z j \ {a, b}).card :=
  Finset.one_le_prod' fun j _ => one_le_card_sdiff_pair (hZ j) (hgood j)

/-- A good pair one of whose factors is at least `2` contributes a term that is at least `2`. -/
private lemma two_le_prod_sdiff_pair (hZ : ∀ j, (Z j).card = 2) (hgood : ∀ j, Z j ≠ {a, b})
    {j₀ : Fin 3} (h2 : 2 ≤ (Z j₀ \ {a, b}).card) :
    2 ≤ ∏ j : Fin 3, (Z j \ {a, b}).card := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j₀)]
  calc (2 : ℕ) = 2 * 1 := (mul_one 2).symm
    _ ≤ (Z j₀ \ {a, b}).card * ∏ j ∈ Finset.univ.erase j₀, (Z j \ {a, b}).card :=
        Nat.mul_le_mul h2
          (Finset.one_le_prod' fun j _ => one_le_card_sdiff_pair (hZ j) (hgood j))

/-- One term of a double sum of naturals is at most the whole sum. -/
private lemma single_term_le (F : ℕ → ℕ → ℕ) (ha : a ∈ X) (hb : b ∈ Y) :
    F a b ≤ ∑ x ∈ X, ∑ y ∈ Y, F x y :=
  le_trans (Finset.single_le_sum (f := F a) (fun _ _ => Nat.zero_le _) hb)
    (Finset.single_le_sum (f := fun x => ∑ y ∈ Y, F x y) (fun _ _ => Nat.zero_le _) ha)

/-- Two terms of a double sum of naturals at distinct index pairs are together at most the whole
sum. -/
private lemma two_terms_le (F : ℕ → ℕ → ℕ) {a₁ b₁ a₂ b₂ : ℕ}
    (ha₁ : a₁ ∈ X) (hb₁ : b₁ ∈ Y) (ha₂ : a₂ ∈ X) (hb₂ : b₂ ∈ Y)
    (hne : (a₁, b₁) ≠ (a₂, b₂)) :
    F a₁ b₁ + F a₂ b₂ ≤ ∑ x ∈ X, ∑ y ∈ Y, F x y := by
  rw [← Finset.sum_product']
  have hsub : ({(a₁, b₁), (a₂, b₂)} : Finset (ℕ × ℕ)) ⊆ X ×ˢ Y := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [Finset.mem_product, ha₁, hb₁, ha₂, hb₂]
  calc F a₁ b₁ + F a₂ b₂
      = ∑ p ∈ ({(a₁, b₁), (a₂, b₂)} : Finset (ℕ × ℕ)), F p.1 p.2 :=
        (Finset.sum_pair (f := fun p : ℕ × ℕ => F p.1 p.2) hne).symm
    _ ≤ ∑ p ∈ X ×ˢ Y, F p.1 p.2 := Finset.sum_le_sum_of_subset hsub

/-- **The combinatorial core of Lemma 6.** For any five two-element sets of colors, the quantity
computed by the product formula for `K₂,₃` is at least `2`.

Together with `col_completeBipartite_two_three` and `colConst_completeBipartite_two_three_two`
this says exactly that `K₂,₃` is 2-monophilic. -/
theorem two_le_sum_prod_sdiff_pair (hX : X.card = 2) (hY : Y.card = 2)
    (hZ : ∀ j, (Z j).card = 2) :
    2 ≤ ∑ x ∈ X, ∑ y ∈ Y, ∏ j : Fin 3, (Z j \ {x, y}).card := by
  set F : ℕ → ℕ → ℕ := fun x y => ∏ j : Fin 3, (Z j \ {x, y}).card with hF
  -- Diagonal pairs are always good: `{c, c}` is a singleton, but the right lists have two
  -- elements.
  have hdiag : ∀ c : ℕ, ∀ j, Z j ≠ {c, c} := by
    intro c j h
    have hc := hZ j
    rw [h] at hc
    simp at hc
  by_cases hI : ∃ p, p ∈ X ∧ p ∈ Y
  · obtain ⟨p, hpX, hpY⟩ := hI
    by_cases hJ : ∃ j, p ∉ Z j
    · -- Some right list avoids the common color `p`: the single term `(p, p)` is already `≥ 2`.
      obtain ⟨j₀, hj₀⟩ := hJ
      exact le_trans
        (two_le_prod_sdiff_pair hZ (hdiag p) (two_le_card_sdiff_pair (hZ j₀) hj₀ hj₀))
        (single_term_le F hpX hpY)
    · -- Every right list contains `p`. Then `(p, p)` and any pair avoiding `p` are both good.
      push Not at hJ
      obtain ⟨u, huX, hup⟩ := exists_mem_ne_of_card_eq_two hX p
      obtain ⟨v, hvY, hvp⟩ := exists_mem_ne_of_card_eq_two hY p
      have hgood : ∀ j, Z j ≠ {u, v} := by
        intro j h
        have hp : p ∈ Z j := hJ j
        rw [h] at hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hup rfl
        · exact hvp rfl
      calc (2 : ℕ) = 1 + 1 := rfl
        _ ≤ F p p + F u v := Nat.add_le_add (one_le_prod_sdiff_pair hZ (hdiag p))
              (one_le_prod_sdiff_pair hZ hgood)
        _ ≤ _ := two_terms_le F hpX hpY huX hvY
              (fun h => hup (congrArg Prod.fst h).symm)
  · -- `X` and `Y` are disjoint: write `X = {p, q}` and `Y = {r, s}` with `p, q, r, s` distinct.
    push Not at hI
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hX
    obtain ⟨r, s, hrs, rfl⟩ := Finset.card_eq_two.mp hY
    have hpX : p ∈ ({p, q} : Finset ℕ) := by simp
    have hqX : q ∈ ({p, q} : Finset ℕ) := by simp
    have hrY : r ∈ ({r, s} : Finset ℕ) := by simp
    have hsY : s ∈ ({r, s} : Finset ℕ) := by simp
    have hpr : p ≠ r := fun h => hI p hpX (h ▸ hrY)
    have hps : p ≠ s := fun h => hI p hpX (h ▸ hsY)
    have hqr : q ≠ r := fun h => hI q hqX (h ▸ hrY)
    have hqs : q ≠ s := fun h => hI q hqX (h ▸ hsY)
    -- Two good pairs among the four suffice.
    have key2 : ∀ a₁ b₁ a₂ b₂ : ℕ, a₁ ∈ ({p, q} : Finset ℕ) → b₁ ∈ ({r, s} : Finset ℕ) →
        a₂ ∈ ({p, q} : Finset ℕ) → b₂ ∈ ({r, s} : Finset ℕ) → (a₁, b₁) ≠ (a₂, b₂) →
        (∀ j, Z j ≠ {a₁, b₁}) → (∀ j, Z j ≠ {a₂, b₂}) →
        2 ≤ ∑ x ∈ ({p, q} : Finset ℕ), ∑ y ∈ ({r, s} : Finset ℕ), F x y := by
      intro a₁ b₁ a₂ b₂ h₁ h₂ h₃ h₄ hne g₁ g₂
      calc (2 : ℕ) = 1 + 1 := rfl
        _ ≤ F a₁ b₁ + F a₂ b₂ := Nat.add_le_add (one_le_prod_sdiff_pair hZ g₁)
              (one_le_prod_sdiff_pair hZ g₂)
        _ ≤ _ := two_terms_le F h₁ h₂ h₃ h₄ hne
    -- Alternatively, a good pair whose "opposite" pair occurs as a right list suffices on its own.
    have key1 : ∀ a₁ b₁ a₂ b₂ : ℕ, a₁ ∈ ({p, q} : Finset ℕ) → b₁ ∈ ({r, s} : Finset ℕ) →
        (∀ j, Z j ≠ {a₁, b₁}) → (¬ ∀ j, Z j ≠ {a₂, b₂}) →
        a₁ ≠ a₂ → a₁ ≠ b₂ → b₁ ≠ a₂ → b₁ ≠ b₂ →
        2 ≤ ∑ x ∈ ({p, q} : Finset ℕ), ∑ y ∈ ({r, s} : Finset ℕ), F x y := by
      intro a₁ b₁ a₂ b₂ h₁ h₂ g₁ g₂ e₁ e₂ e₃ e₄
      push Not at g₂
      obtain ⟨j₀, hj₀⟩ := g₂
      refine le_trans (two_le_prod_sdiff_pair hZ g₁
        (two_le_card_sdiff_pair (hZ j₀) ?_ ?_)) (single_term_le F h₁ h₂)
      · rw [hj₀]; simp [e₁, e₂]
      · rw [hj₀]; simp [e₃, e₄]
    by_cases g₁ : ∀ j, Z j ≠ {p, r}
    · by_cases g₂ : ∀ j, Z j ≠ {q, s}
      · exact key2 p r q s hpX hrY hqX hsY (fun h => hpq (congrArg Prod.fst h)) g₁ g₂
      · exact key1 p r q s hpX hrY g₁ g₂ hpq hps hqr.symm hrs
    · by_cases g₂ : ∀ j, Z j ≠ {q, s}
      · exact key1 q s p r hqX hsY g₂ g₁ hpq.symm hqr hps.symm hrs.symm
      · by_cases g₃ : ∀ j, Z j ≠ {p, s}
        · by_cases g₄ : ∀ j, Z j ≠ {q, r}
          · exact key2 p s q r hpX hsY hqX hrY (fun h => hpq (congrArg Prod.fst h)) g₃ g₄
          · exact key1 p s q r hpX hsY g₃ g₄ hpq hpr hqs.symm hrs.symm
        · by_cases g₄ : ∀ j, Z j ≠ {q, r}
          · exact key1 q r p s hqX hrY g₄ g₃ hpq.symm hqs hpr.symm hrs
          · -- All four pairs occur as right lists, but there are only three of those.
            exfalso
            push Not at g₁ g₂ g₃ g₄
            obtain ⟨j₁, e₁⟩ := g₁
            obtain ⟨j₂, e₂⟩ := g₂
            obtain ⟨j₃, e₃⟩ := g₃
            obtain ⟨j₄, e₄⟩ := g₄
            have pairne : ∀ u v u' v' : ℕ, u ∉ ({u', v'} : Finset ℕ) →
                ({u, v} : Finset ℕ) ≠ {u', v'} := by
              intro u v u' v' h hcon
              exact h (hcon ▸ Finset.mem_insert_self u {v})
            have pairne' : ∀ u v u' v' : ℕ, v ∉ ({u', v'} : Finset ℕ) →
                ({u, v} : Finset ℕ) ≠ {u', v'} := by
              intro u v u' v' h hcon
              exact h (hcon ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
            have hZne : ∀ i k : Fin 3, Z i ≠ Z k → i ≠ k := fun i k h e => h (by rw [e])
            have d₁₂ : j₁ ≠ j₂ := hZne _ _ (by
              rw [e₁, e₂]; exact pairne p r q s (by simp [hpq, hps]))
            have d₁₃ : j₁ ≠ j₃ := hZne _ _ (by
              rw [e₁, e₃]; exact pairne' p r p s (by simp [hpr.symm, hrs]))
            have d₁₄ : j₁ ≠ j₄ := hZne _ _ (by
              rw [e₁, e₄]; exact pairne p r q r (by simp [hpq, hpr]))
            have d₂₃ : j₂ ≠ j₃ := hZne _ _ (by
              rw [e₂, e₃]; exact pairne q s p s (by simp [hpq.symm, hqs]))
            have d₂₄ : j₂ ≠ j₄ := hZne _ _ (by
              rw [e₂, e₄]; exact pairne' q s q r (by simp [hqs.symm, hrs.symm]))
            have d₃₄ : j₃ ≠ j₄ := hZne _ _ (by
              rw [e₃, e₄]; exact pairne p s q r (by simp [hpq, hpr]))
            have b₁ : (j₁ : ℕ) < 3 := j₁.isLt
            have b₂ : (j₂ : ℕ) < 3 := j₂.isLt
            have b₃ : (j₃ : ℕ) < 3 := j₃.isLt
            have b₄ : (j₄ : ℕ) < 3 := j₄.isLt
            have v₁₂ : (j₁ : ℕ) ≠ (j₂ : ℕ) := fun h => d₁₂ (Fin.val_injective h)
            have v₁₃ : (j₁ : ℕ) ≠ (j₃ : ℕ) := fun h => d₁₃ (Fin.val_injective h)
            have v₁₄ : (j₁ : ℕ) ≠ (j₄ : ℕ) := fun h => d₁₄ (Fin.val_injective h)
            have v₂₃ : (j₂ : ℕ) ≠ (j₃ : ℕ) := fun h => d₂₃ (Fin.val_injective h)
            have v₂₄ : (j₂ : ℕ) ≠ (j₄ : ℕ) := fun h => d₂₄ (Fin.val_injective h)
            have v₃₄ : (j₃ : ℕ) ≠ (j₄ : ℕ) := fun h => d₃₄ (Fin.val_injective h)
            omega

end Core

/-- **Lemma 6 of Kirov–Naimi.** `K₂,₃` is 2-monophilic: every assignment of two-element color
lists admits at least `col(K₂,₃, 2) = 2` proper colorings. -/
theorem monophilic_K23 :
    (completeBipartiteGraph (Fin 2) (Fin 3)).Monophilic 2 := by
  intro L hL
  rw [colConst_completeBipartite_two_three_two, col_completeBipartite_two_three]
  exact two_le_sum_prod_sdiff_pair (hL _) (hL _) fun j => hL _

/-! ### Sanity checks -/

section Guards

private def mkL (x y u v w : Finset ℕ) : ListAssignment (Fin 2 ⊕ Fin 3) :=
  Sum.elim ![x, y] ![u, v, w]

private def rhsL (L : ListAssignment (Fin 2 ⊕ Fin 3)) : ℕ :=
  ∑ a ∈ L (Sum.inl 0), ∑ b ∈ L (Sum.inl 1), ∏ j : Fin 3, (L (Sum.inr j) \ {a, b}).card

#guard (completeBipartiteGraph (Fin 2) (Fin 3)).colConst 2 = 2

-- The product formula, on representatives of all three cases of the analysis.
#guard (completeBipartiteGraph (Fin 2) (Fin 3)).col (mkL {0,1} {0,1} {0,1} {0,1} {0,1})
  = rhsL (mkL {0,1} {0,1} {0,1} {0,1} {0,1})
-- `X = Y`
#guard (completeBipartiteGraph (Fin 2) (Fin 3)).col (mkL {0,1} {0,1} {2,3} {0,4} {1,5})
  = rhsL (mkL {0,1} {0,1} {2,3} {0,4} {1,5})
-- `|X ∩ Y| = 1`
#guard (completeBipartiteGraph (Fin 2) (Fin 3)).col (mkL {0,1} {0,2} {0,3} {0,4} {0,5})
  = rhsL (mkL {0,1} {0,2} {0,3} {0,4} {0,5})
-- `X ∩ Y = ∅`, the tight configuration killing three of the four pairs
#guard (completeBipartiteGraph (Fin 2) (Fin 3)).col (mkL {0,1} {2,3} {0,2} {0,3} {1,2})
  = rhsL (mkL {0,1} {2,3} {0,2} {0,3} {1,2})
#guard (completeBipartiteGraph (Fin 2) (Fin 3)).col (mkL {0,1} {2,3} {0,2} {0,3} {1,2}) = 2

end Guards

end SimpleGraph
