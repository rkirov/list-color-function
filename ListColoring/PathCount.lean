/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Path
import ListColoring.Recurrence

/-!
# Counting colorings of a path from an `(n, n-1)`-list assignment

This is the graph-theoretic half of Lemma 3 of Kirov–Naimi: it identifies the number of colorings
of a path from a type A / type B `(n, n-1)`-list assignment with the recurrences `A_k`, `B_k` of
`ListColoring.Recurrence`.

Recall the setup (paper, p. 3): an `(n, n-1)`-list assignment for a path assigns `n`-color lists to
the interior vertices and `(n-1)`-color lists to the two terminal vertices, with the interior lists
all equal to a common set `S` and the terminal lists subsets of `S`. Such a terminal list is
therefore `S \ {x}` for a unique `x ∈ S`, so an `(n,n-1)`-assignment is determined up to renaming by
the pair `(x, y)` of colors missing at the two ends. It is **type A** when `x = y` and **type B**
otherwise.

Writing `n = m + 2` throughout (as in `ListColoring.Recurrence`), `pathAssign k n x y` is the
`(n,n-1)`-assignment on the path of length `k` missing `x` at `pathEnd` and `y` at `pathStart`.

The whole content is the single recursion `inducedList_pathAssign`: peeling the endpoint off and
giving it color `c` turns an `(x, y)`-assignment on `P_{k+1}` into a `(c, y)`-assignment on `P_k`.
Since `c` ranges over `S \ {x}`, the type A case (`x = y`) never produces `c = y` and so contributes
`(n-1)` type B terms, while the type B case (`x ≠ y`) produces exactly one type A term and `(n-2)`
type B terms. These are precisely the paper's equations (2) and (3).

## Main results

* `ListColoring.inducedList_pathAssign` : the recursion on list assignments
* `ListColoring.col_pathAssign` : `col(P_k, L) = A_k` for type A and `B_k` for type B
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With no edges, every choice from the lists is a proper coloring. -/
theorem col_bot (M : ListAssignment V) :
    (⊥ : SimpleGraph V).col M = ∏ v, (M v).card := by
  rw [col, colorings, Finset.filter_true_of_mem, Fintype.card_piFinset]
  intro f _ v w hvw
  exact absurd hvw (by simp)

end SimpleGraph

namespace ListColoring

open SimpleGraph

/-- Lists of the non-terminal part: every vertex gets the full palette `range n`, except the far
endpoint `pathStart`, which is missing `y`. -/
def pathInterior : (k : ℕ) → (n y : ℕ) → ListAssignment (PathV k)
  | 0, n, y => fun _ => (range n).erase y
  | k + 1, n, y => fun v =>
      match v with
      | none => range n
      | some w => pathInterior k n y w

/-- The `(n, n-1)`-list assignment on the path of length `k` missing color `x` at `pathEnd` and
color `y` at `pathStart`; type A when `x = y`, type B otherwise. -/
def pathAssign : (k : ℕ) → (n x y : ℕ) → ListAssignment (PathV k)
  | 0, n, x, y => fun _ => ((range n).erase x).erase y
  | k + 1, n, x, y => fun v =>
      match v with
      | none => (range n).erase x
      | some w => pathInterior k n y w

@[simp] lemma pathAssign_succ_none (k n x y : ℕ) :
    pathAssign (k + 1) n x y none = (range n).erase x := rfl

instance : Unique (PathV 0) := inferInstanceAs (Unique Unit)

/-- A path of length `0` is a single vertex and no edges. -/
lemma col_pathG_zero (M : ListAssignment (PathV 0)) :
    (pathG 0).col M = (M default).card := by
  rw [col, colorings, Finset.filter_true_of_mem, Fintype.card_piFinset]
  · simp
  · intro f _ v w hvw
    exact absurd hvw (by simp [pathG])

/-- **The recursion.** Peeling the endpoint off `P_{k+1}` and giving it the color `c` leaves, on
`P_k`, exactly the `(n,n-1)`-assignment missing `c` at the new endpoint and `y` at the far end. -/
theorem inducedList_pathAssign (k n x y c : ℕ) :
    (pathG (k + 1)).inducedList (pathAssign (k + 1) n x y) c = pathAssign k n c y := by
  funext w
  rw [inducedList_pathG_succ]
  match k, w with
  -- These two branches are closed by definitional unfolding, not by `simp`. The condition
  -- `inducedList_pathG_succ` leaves is `w = pathEnd k`, which `reduceIte` will not evaluate
  -- because `pathEnd k` does not reduce on its own; and `rw`/`simp` cannot be pointed at it
  -- either, since the target is not type-correct at `implicit` transparency across the
  -- `PathV 0` / `Unit` boundary (`ListColoring.PathColorable`'s module docstring has the general
  -- version of this). `exact` and `rfl` unify at default transparency and go straight through.
  | 0, () => exact Finset.erase_right_comm
  | _ + 1, none => rfl
  | _ + 1, some w' => simp [pathAssign, pathInterior, pathEnd]

/-- **Lemma 3(a), graph side.** The number of colorings of a path of length `k` from an
`(n, n-1)`-list assignment is `A_k` if the assignment is type A and `B_k` if it is type B. -/
theorem col_pathAssign (m : ℕ) :
    ∀ (k x y : ℕ), x < m + 2 → y < m + 2 →
      (pathG k).col (pathAssign k (m + 2) x y) = if x = y then pathA m k else pathB m k := by
  intro k
  induction k with
  | zero =>
    intro x y hx hy
    rw [col_pathG_zero]
    show (((range (m + 2)).erase x).erase y).card = _
    by_cases hxy : x = y
    · subst hxy
      rw [Finset.erase_idem, Finset.card_erase_of_mem (Finset.mem_range.mpr hx),
        Finset.card_range, if_pos rfl, pathA_zero]
      omega
    · rw [Finset.card_erase_of_mem
          (Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_range.mpr hy⟩),
        Finset.card_erase_of_mem (Finset.mem_range.mpr hx), Finset.card_range,
        if_neg hxy, pathB_zero]
      omega
  | succ k ih =>
    intro x y hx hy
    rw [col_pathG_succ]
    simp only [pathEnd_succ, pathAssign_succ_none]
    have hterm : ∀ c ∈ (range (m + 2)).erase x,
        (pathG k).col ((pathG (k + 1)).inducedList (pathAssign (k + 1) (m + 2) x y) c)
          = if c = y then pathA m k else pathB m k := by
      intro c hc
      rw [inducedList_pathAssign]
      exact ih c y (Finset.mem_range.mp (Finset.mem_of_mem_erase hc)) hy
    rw [Finset.sum_congr rfl hterm]
    have hxr : x ∈ range (m + 2) := Finset.mem_range.mpr hx
    by_cases hxy : x = y
    · -- type A: `y` is the erased color, so every term is type B
      subst hxy
      have : ∀ c ∈ (range (m + 2)).erase x, (if c = x then pathA m k else pathB m k) = pathB m k :=
        fun c hc => if_neg (Finset.ne_of_mem_erase hc)
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem hxr,
        Finset.card_range, smul_eq_mul]
      have hm : m + 2 - 1 = m + 1 := by omega
      rw [if_pos rfl, hm, pathA_succ]
    · -- type B: exactly one term is type A, the rest are type B
      have hymem : y ∈ (range (m + 2)).erase x :=
        Finset.mem_erase.mpr ⟨Ne.symm hxy, Finset.mem_range.mpr hy⟩
      rw [← Finset.add_sum_erase _ _ hymem, if_pos rfl]
      have : ∀ c ∈ ((range (m + 2)).erase x).erase y,
          (if c = y then pathA m k else pathB m k) = pathB m k :=
        fun c hc => if_neg (Finset.ne_of_mem_erase hc)
      rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul,
        Finset.card_erase_of_mem hymem, Finset.card_erase_of_mem hxr, Finset.card_range]
      have hm : m + 2 - 1 - 1 = m := by omega
      rw [hm, pathB_succ, if_neg hxy]

end ListColoring
