/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Cacti.Rooted

/-!
# Uniform rooted counts

The normalizers of the block induction are rooted counts against the constant list assignment.
By colour-permutation symmetry these do not depend on the root's colour, so each equals
`G.colConst k / k`; we record the symmetry and the sum identity, avoiding division.
-/

namespace ListColoring

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Colour-permutation symmetry**: rooted counts against the constant list assignment do not
depend on the root's colour. Transposing the two colours is a bijection on colorings. -/
theorem rootedCol_constList_eq (k : ℕ) (r : V) {c d : ℕ} (hc : c ∈ range k)
    (hd : d ∈ range k) :
    rootedCol G (constList V k) r c = rootedCol G (constList V k) r d := by
  rw [rootedCol, rootedCol]
  refine Finset.card_nbij' (fun f => fun v => Equiv.swap c d (f v))
    (fun f => fun v => Equiv.swap c d (f v)) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, SimpleGraph.mem_colorings_iff] at hf ⊢
    obtain ⟨⟨hmem, hprop⟩, hr⟩ := hf
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v
      simp only [constList_apply, Finset.mem_range] at hmem ⊢
      by_cases hfc : f v = c
      · rw [hfc, Equiv.swap_apply_left]
        exact Finset.mem_range.mp hd
      · by_cases hfd : f v = d
        · rw [hfd, Equiv.swap_apply_right]
          exact Finset.mem_range.mp hc
        · rw [Equiv.swap_apply_of_ne_of_ne hfc hfd]
          exact hmem v
    · intro v u hadj
      exact fun h => hprop v u hadj ((Equiv.swap c d).injective h)
    · rw [hr, Equiv.swap_apply_left]
  · intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, SimpleGraph.mem_colorings_iff] at hf ⊢
    obtain ⟨⟨hmem, hprop⟩, hr⟩ := hf
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v
      simp only [constList_apply, Finset.mem_range] at hmem ⊢
      by_cases hfc : f v = c
      · rw [hfc, Equiv.swap_apply_left]
        exact Finset.mem_range.mp hd
      · by_cases hfd : f v = d
        · rw [hfd, Equiv.swap_apply_right]
          exact Finset.mem_range.mp hc
        · rw [Equiv.swap_apply_of_ne_of_ne hfc hfd]
          exact hmem v
    · intro v u hadj
      exact fun h => hprop v u hadj ((Equiv.swap c d).injective h)
    · rw [hr, Equiv.swap_apply_right]
  · intro f hf
    funext v
    exact Equiv.swap_apply_self _ _ _
  · intro f hf
    funext v
    exact Equiv.swap_apply_self _ _ _

/-- The uniform rooted count, summed over the palette, is the uniform total count. -/
theorem sum_rootedCol_constList (k : ℕ) (r : V) :
    ∑ c ∈ range k, rootedCol G (constList V k) r c = G.colConst k :=
  (col_eq_sum_rootedCol G (constList V k) r).symm

/-- Each uniform rooted count, multiplied by the palette size, is the uniform total count. -/
theorem card_mul_rootedCol_constList (k : ℕ) (r : V) {c : ℕ} (hc : c ∈ range k) :
    k * rootedCol G (constList V k) r c = G.colConst k := by
  rw [← sum_rootedCol_constList G k r]
  rw [Finset.sum_congr rfl (fun d hd => rootedCol_constList_eq G k r hd hc)]
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end ListColoring
