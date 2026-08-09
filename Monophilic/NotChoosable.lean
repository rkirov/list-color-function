/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.Basic

/-!
# `K_{n,nⁿ}` is `n`-colorable but not `n`-choosable

This is the combinatorial foundation of Kirov–Naimi §5, where the graphs `H_{n+1}` — which are
`(n+1)`-choosable but not `(n+1)`-monophilic — are assembled out of copies of a complete bipartite
graph carrying a list assignment with **no** colorings at all. It is also the classical
Erdős–Rubin–Taylor separation between colorability and choosability: bipartite graphs have
chromatic number `2`, but their choice number is unbounded.

The graph is `K_{n,nⁿ}`, realised as `completeBipartiteGraph (Fin n) (Fin n → Fin n)`: the right
side is indexed by *functions* `Fin n → Fin n`, of which there are `n ^ n`
(`SimpleGraph.ERT.card_right`). The list assignment `L₀` is

* `L₀ (inl i) = {i * n, i * n + 1, …, i * n + (n-1)}` — the `i`-th block of `n` consecutive colors,
  so the `n` left lists are pairwise disjoint;
* `L₀ (inr φ) = {i * n + φ i : i : Fin n}` — one color out of each block, selected by `φ`.

Every list has exactly `n` colors, and there is no proper coloring: a coloring `f` of the left side
picks out exactly one `φ : Fin n → Fin n` with `f (inl i) = i * n + φ i`, and then the single right
vertex `inr φ` — which is adjacent to every left vertex — has its whole list already used up.

## Main results

* `SimpleGraph.ERT.isNListAssignment_L₀` : `L₀` is an `n`-list assignment
* `SimpleGraph.ERT.col_L₀_eq_zero` : `col(K_{n,nⁿ}, L₀) = 0`
* `SimpleGraph.ERT.not_choosable` : `K_{n,nⁿ}` is not `n`-choosable
* `SimpleGraph.ERT.colorable` : `K_{n,nⁿ}` is `n`-colorable as soon as `2 ≤ n`
* `SimpleGraph.ERT.not_monophilic` : hence `K_{n,nⁿ}` is not `n`-monophilic for `2 ≤ n`

## Implementation notes

Everything lives in the namespace `SimpleGraph.ERT` so that the auxiliary `DecidableRel` instance
for `completeBipartiteGraph` cannot collide with declarations of the same purpose elsewhere in the
library.

Note that `col_L₀_eq_zero` and `not_choosable` need no hypothesis on `n` whatsoever: for `n = 0`
the vertex `inr φ` (the empty function) simply gets the empty list.
-/

open Finset

namespace SimpleGraph
namespace ERT

/-- Adjacency in a complete bipartite graph is decidable: it only inspects which side each vertex
lies on. -/
instance instDecidableRelCompleteBipartiteAdj (V W : Type*) :
    DecidableRel (completeBipartiteGraph V W).Adj :=
  fun v w => inferInstanceAs (Decidable (v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft))

/-! ### Arithmetic of the color blocks

Colors are laid out as `n` consecutive blocks of length `n`: the pair `(i, j) : Fin n × Fin n`
names the color `i * n + j`. The two projections are recovered by `Nat.div` and `Nat.mod`. -/

/-- A color `a * n + c` with `c < n` determines both `a` and `c`. -/
private lemma block_eq_imp {n a b c d : ℕ} (hc : c < n) (hd : d < n)
    (h : a * n + c = b * n + d) : a = b ∧ c = d := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le c) hc
  have hdiv : ∀ x y : ℕ, y < n → (x * n + y) / n = x := by
    intro x y hy
    rw [Nat.add_comm (x * n) y, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hy, Nat.zero_add]
  have hmod : ∀ x y : ℕ, y < n → (x * n + y) % n = y := by
    intro x y hy
    rw [Nat.add_comm (x * n) y, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  exact ⟨by rw [← hdiv a c hc, ← hdiv b d hd, h], by rw [← hmod a c hc, ← hmod b d hd, h]⟩

variable (n : ℕ)

/-- `K_{n,nⁿ}`, the complete bipartite graph whose right side is indexed by the functions
`Fin n → Fin n`. -/
abbrev K : SimpleGraph (Fin n ⊕ (Fin n → Fin n)) :=
  completeBipartiteGraph (Fin n) (Fin n → Fin n)

/-- The right side of `K_{n,nⁿ}` really does have `nⁿ` vertices. -/
theorem card_right : Fintype.card (Fin n → Fin n) = n ^ n := by
  simp

/-- The Erdős–Rubin–Taylor list assignment on `K_{n,nⁿ}`, called `L₀` in Kirov–Naimi §5.

The `i`-th left vertex gets the `i`-th block `{i*n, …, i*n + (n-1)}` of `n` consecutive colors
(so the left lists are pairwise disjoint), and the right vertex indexed by `φ` gets the transversal
`{i*n + φ i : i}` picking one color out of each block. -/
def L₀ : ListAssignment (Fin n ⊕ (Fin n → Fin n)) :=
  Sum.elim (fun i => (univ : Finset (Fin n)).image fun j : Fin n => i.val * n + j.val)
    (fun φ => (univ : Finset (Fin n)).image fun i : Fin n => i.val * n + (φ i).val)

@[simp] lemma L₀_inl (i : Fin n) :
    L₀ n (Sum.inl i) = (univ : Finset (Fin n)).image fun j : Fin n => i.val * n + j.val := rfl

@[simp] lemma L₀_inr (φ : Fin n → Fin n) :
    L₀ n (Sum.inr φ) = (univ : Finset (Fin n)).image fun i : Fin n => i.val * n + (φ i).val := rfl

/-- The `i`-th block map `j ↦ i*n + j` is injective. -/
lemma blockMap_injective (i : Fin n) :
    Function.Injective fun j : Fin n => i.val * n + j.val := fun j j' h =>
  Fin.val_injective (block_eq_imp j.isLt j'.isLt h).2

/-- A transversal map `i ↦ i*n + φ i` is injective: the block index is recoverable. -/
lemma transversalMap_injective (φ : Fin n → Fin n) :
    Function.Injective fun i : Fin n => i.val * n + (φ i).val := fun i i' h =>
  Fin.val_injective (block_eq_imp (φ i).isLt (φ i').isLt h).1

/-- Every list of `L₀` has exactly `n` colors. -/
theorem isNListAssignment_L₀ : IsNListAssignment (L₀ n) n := by
  rintro (i | φ)
  · rw [L₀_inl, Finset.card_image_of_injective _ (blockMap_injective n i), Finset.card_univ,
      Fintype.card_fin]
  · rw [L₀_inr, Finset.card_image_of_injective _ (transversalMap_injective n φ), Finset.card_univ,
      Fintype.card_fin]

/-- **The key computation**: `col(K_{n,nⁿ}, L₀) = 0`, i.e. `L₀` admits no proper coloring at all.

Any choice from the left lists is `f (inl i) = i*n + φ i` for a unique `φ : Fin n → Fin n`, and the
list of the right vertex `inr φ` is *exactly* the set of colors so used. Since `inr φ` is adjacent
to every left vertex, it has nothing left to take. -/
theorem col_L₀_eq_zero : (K n).col (L₀ n) = 0 := by
  rw [col_eq_zero_iff]
  intro f hf hproper
  -- Read off the left-hand colors as a function `φ : Fin n → Fin n`.
  have hleft : ∀ i : Fin n, ∃ j : Fin n, f (Sum.inl i) = i.val * n + j.val := by
    intro i
    have h := hf (Sum.inl i)
    simp only [L₀_inl, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨j, hj⟩ := h
    exact ⟨j, hj.symm⟩
  choose φ hφ using hleft
  -- The vertex `inr φ` must take a color already used on the left.
  have hright := hf (Sum.inr φ)
  simp only [L₀_inr, Finset.mem_image, Finset.mem_univ, true_and] at hright
  obtain ⟨i, hi⟩ := hright
  have hadj : (K n).Adj (Sum.inl i) (Sum.inr φ) := by simp
  exact hproper hadj (by rw [hφ i]; exact hi)

/-- `K_{n,nⁿ}` is **not** `n`-choosable, witnessed by `L₀`. This is the Erdős–Rubin–Taylor
separation and the starting point of Kirov–Naimi §5. -/
theorem not_choosable : ¬ (K n).Choosable n := by
  intro h
  have hpos := h (L₀ n) (isNListAssignment_L₀ n)
  rw [col_L₀_eq_zero] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- `K_{n,nⁿ}` is bipartite, hence `2`-colorable. -/
theorem colorable_two : (K n).Colorable 2 := by
  simpa using (CompleteBipartiteGraph.bicoloring (Fin n) (Fin n → Fin n)).colorable

/-- `K_{n,nⁿ}` is `n`-colorable once `2 ≤ n`. Combined with `not_choosable`, the failure of
`n`-choosability is genuinely a *list* phenomenon and not a chromatic one. -/
theorem colorable (hn : 2 ≤ n) : (K n).Colorable n := (colorable_two n).mono hn

/-- Since `K_{n,nⁿ}` is `n`-colorable but not `n`-choosable, it is not `n`-monophilic: it sits in
the middle regime `χ(G) ≤ n < χ_ℓ(G)` of Kirov–Naimi p. 2. -/
theorem not_monophilic (hn : 2 ≤ n) : ¬ (K n).Monophilic n :=
  not_monophilic_of_colorable_of_not_choosable (colorable n hn) (not_choosable n)

/-! ### Numerical sanity checks

Only `n ≤ 2` is evaluated: `K_{3,27}` has 30 vertices and is far out of reach of kernel reduction.
-/

-- `K_{1,1}`: a single edge, both lists `{0}`.
#guard (K 1).col (L₀ 1) = 0
#guard ∀ v, ((L₀ 1) v).card = 1

-- `K_{2,4}`: left lists `{0,1}` and `{2,3}`, right lists the four transversals.
#guard (K 2).col (L₀ 2) = 0
#guard (L₀ 2) (Sum.inl 0) = {0, 1}
#guard (L₀ 2) (Sum.inl 1) = {2, 3}
#guard (L₀ 2) (Sum.inr id) = {0, 3}
#guard (L₀ 2) (Sum.inr fun _ => 0) = {0, 2}
-- ... while the *constant* 2-list assignment has two colorings, so `K_{2,4}` is 2-colorable.
#guard (K 2).colConst 2 = 2
#guard Fintype.card (Fin 2 → Fin 2) = 2 ^ 2

end ERT
end SimpleGraph
