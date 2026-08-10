/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.Cycle
import ListColoring.PathMinimizing
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Theorem 1 of Kirov–Naimi: cycles are enumeratively chromatic-choosable at `n`

This file proves the main theorem of §3 of R. Kirov and R. Naimi, *List coloring and `n`-monophilic
graphs* (arXiv:1004.5183): every cycle is enumeratively chromatic-choosable at `n`.

## The shape of the argument

Fix a cycle `C` and an `n`-list assignment `M` on it. Deleting one vertex `v` of `C` and summing
over the color given to `v` (`ListColoring.col_closePath_succ`) writes

  `col(C, M) = ∑ c ∈ M v, col(P, M_c)`,

where `P = C − v` is a path and `M_c` is the assignment induced by giving `v` the color `c`: the two
terminal vertices of `P` (the former neighbors of `v`) lose the color `c` from their lists, if they
had it, and every other list is unchanged. So `M_c` gives `n` colors to every interior vertex of `P`
and `n` or `n − 1` colors to each terminal vertex. Shrinking the terminal lists to exactly `n − 1`
colors where necessary produces an `(n, n-1)`-list assignment below `M_c`, and Lemma 3(b)
(`ListColoring.min_pathA_pathB_le_col`) bounds its count from below by `min (A, B)`. That is the
content of `ListColoring.min_pathA_pathB_le_col_inducedList`.

Since `col(C, n) = n · A` (`ListColoring.colConst_closePath_succ`), this already settles the case
where `min (A, B) = A`, i.e. where the path `P` has odd length — equivalently where `C` has an
**odd number of vertices**. This is Case 1 of the paper, and it needs no hypothesis beyond `n ≥ 2`
(`ListColoring.ecc_closePath_of_odd`).

For an even number of vertices `min (A, B) = B = A − 1`, and the above only gives `n·A − n`. Case 2
of the paper recovers the missing `n` for `n ≥ 3`. Either every term is already `≥ A` and we are
done, or some `c₀` gives fewer. In the latter case Lemma 3(b), Lemma 3(c)
(`ListColoring.isPathShape_parity_of_minimizing`) and Lemma 4 (`ListColoring.col_lt_col_of_ssubset`)
together force `M_{c₀}` to be *exactly* a type B `(n, n-1)`-assignment
(`ListColoring.isPathShape_of_col_lt`), with palette `S`, and `c₀ ∉ S` while `c₀` belongs to both of
the original terminal lists. That single color `c₀` then witnesses that no *other* `M_c` can be
type B, so every other term is `≥ B + 1 = A`; and the same `c₀` shows that the two terminal lists
of `C − v` are distinct, so one of them differs from `M v`, which produces a color `d` yielding a
term `≥ A + 1`. Summing, `col(C, M) ≥ B + (A + 1) + (n − 2)·A = n·A`.

## Indexing

Following `ListColoring.Cycle`, `closePath (j + 1)` is the cycle on `j + 2` vertices, and deleting
one vertex leaves the path `pathG j` of length `j`. So the paper's cycle of length `k` is
`closePath (k - 1)`, and its `A_{k-2}` is `pathA m (k - 2)` with `n = m + 2`. In particular the
parity of `j` is the parity of the number `j + 2` of vertices of the cycle: `j` odd means an **odd
cycle**.

## Main results

* `ListColoring.min_pathA_pathB_le_col_inducedList` : the reduction of a cycle to a path
* `ListColoring.ecc_closePath_of_odd` : **odd cycles are enumeratively chromatic-choosable at `n`
  for every `n ≥ 2`**
* `ListColoring.ecc_closePath_of_even` : **even cycles are enumeratively chromatic-choosable at `n`
  for every `n ≥ 3`**
* `ListColoring.ecc_closePath` : **every cycle is enumeratively chromatic-choosable at `n` for every
  `n ≥ 3`**

## What is missing

The case `n = 2` for cycles with an even number of vertices is *not* proved here: the paper treats
it by a separate argument via a "forces" relation, which is not formalized. Note that this is not a
degenerate case — `col(C, 2) = 2` for an even cycle, and there really are non-constant minimizing
`2`-assignments (assign `{0,1}` to two adjacent vertices and `{1,2}` to all the others).
-/

open Finset

namespace ListColoring

open SimpleGraph

/-! ### Numerical sanity checks

`closePath (j + 1)` has `j + 2` vertices, so `closePath 2` is the triangle and `closePath 4` is
`C₅`. Both have `j` odd. -/

#guard Fintype.card (PathV 2) = 3        -- `closePath 2` is `C₃`
#guard Fintype.card (PathV 4) = 5        -- `closePath 4` is `C₅`
#guard (closePath 2).colConst 3 = 3 * pathA 1 1   -- `j = 1`, odd
#guard (closePath 4).colConst 3 = 3 * pathA 1 3   -- `j = 3`, odd
#guard (closePath 3).colConst 3 = 3 * pathA 1 2   -- `j = 2`, even
#guard (closePath 5).colConst 3 = 3 * pathA 1 4   -- `j = 4`, even

/-- A test list assignment on `PathV k`: `{0,1,2}` at the vertex numbered `0`, `{1,2,3}` at the
vertex numbered `1`, `{0,1,2}` elsewhere. Deliberately non-constant. -/
private def testM (k : ℕ) : ListAssignment (PathV k) := fun v =>
  if v = pathVtx k 1 then ({1, 2, 3} : Finset ℕ) else ({0, 1, 2} : Finset ℕ)

/-- Another non-constant test assignment, with three distinct lists in a row. -/
private def testM' (k : ℕ) : ListAssignment (PathV k) := fun v =>
  if v = pathVtx k 0 then ({0, 1, 2} : Finset ℕ)
  else if v = pathVtx k 1 then ({1, 2, 3} : Finset ℕ) else ({2, 3, 4} : Finset ℕ)

-- The content of Theorem 1: `col(C, n) ≤ col(C, L)` on concrete non-constant `L`, both parities.
#guard (closePath 2).colConst 3 ≤ (closePath 2).col (testM 2)     -- `C₃`
#guard (closePath 3).colConst 3 ≤ (closePath 3).col (testM 3)     -- `C₄`
#guard (closePath 4).colConst 3 ≤ (closePath 4).col (testM 4)     -- `C₅`
#guard (closePath 5).colConst 3 ≤ (closePath 5).col (testM 5)     -- `C₆`
#guard (closePath 2).colConst 3 ≤ (closePath 2).col (testM' 2)
#guard (closePath 3).colConst 3 ≤ (closePath 3).col (testM' 3)
#guard (closePath 4).colConst 3 ≤ (closePath 4).col (testM' 4)
#guard (closePath 5).colConst 3 ≤ (closePath 5).col (testM' 5)

/-- A stress test for the even case. Deleting the vertex numbered `0` of `C₄` and giving it the
color `3` leaves on the remaining path a genuine **type B** `(3,2)`-assignment — palette
`{0,1,2}`, missing `0` at one end and `1` at the other — so that fibre contributes only `B₂ = 5`,
one less than `A₂ = 6`. This is exactly the situation `ListColoring.isPathShape_of_col_lt`
isolates; note the color `3` lies outside the palette and inside both terminal lists, as the
proof of Case 2 predicts. -/
private def testTypeB : ListAssignment (PathV 3) := fun v =>
  if v = pathVtx 3 0 then ({0, 1, 3} : Finset ℕ)
  else if v = pathVtx 3 1 then ({1, 2, 3} : Finset ℕ)
  else if v = pathVtx 3 2 then ({0, 1, 2} : Finset ℕ)
  else ({0, 2, 3} : Finset ℕ)

#guard (closePath 3).colFix testTypeB (pathEnd 3) 3 = pathB 1 2   -- the short fibre, `5 < A₂ = 6`
#guard (closePath 3).col testTypeB = 29
#guard (closePath 3).colConst 3 ≤ (closePath 3).col testTypeB    -- `18 ≤ 29`

/-- The same stress test one size up, on `C₆`: the fibre of the color `3` is `B₄ = 21 < A₄ = 22`. -/
private def testTypeB' : ListAssignment (PathV 5) := fun v =>
  if v = pathVtx 5 0 then ({0, 1, 3} : Finset ℕ)
  else if v = pathVtx 5 1 then ({1, 2, 3} : Finset ℕ)
  else if v = pathVtx 5 5 then ({0, 2, 3} : Finset ℕ)
  else ({0, 1, 2} : Finset ℕ)

#guard (closePath 5).colFix testTypeB' (pathEnd 5) 3 = pathB 1 4  -- `21 < A₄ = 22`
#guard (closePath 5).col testTypeB' = 115
#guard (closePath 5).colConst 3 ≤ (closePath 5).col testTypeB'   -- `66 ≤ 115`

/-- The paper's remark: an even cycle has a *non-constant* minimizing `2`-assignment, so the
inequality of Theorem 1 can be an equality off the constant assignment. -/
private def testTwo : ListAssignment (PathV 3) := fun v =>
  if v = pathVtx 3 0 ∨ v = pathVtx 3 1 then ({0, 1} : Finset ℕ) else ({1, 2} : Finset ℕ)

#guard (closePath 3).colConst 2 = 2
#guard (closePath 3).col testTwo = 2

-- `n = 2` on an *odd* cycle is vacuous: there is no coloring at all from the constant lists.
#guard (closePath 2).colConst 2 = 0
#guard (closePath 4).colConst 2 = 0

/-! ### The two ends of a path -/

/-- A path of positive length has two distinct terminal vertices. -/
lemma pathEnd_ne_pathStart : ∀ {j : ℕ}, 1 ≤ j → pathEnd j ≠ pathStart j
  | 0, h => absurd h (by omega)
  | _ + 1, _ => fun h => absurd h.symm (some_ne_pathEnd_succ _)

/-! ### The lists induced on the path by deleting a vertex of the cycle -/

variable {j m : ℕ}

/-- The list induced at the terminal vertex `pathEnd j`: it loses the color of the deleted
vertex. -/
lemma inducedList_closePath_pathEnd (j : ℕ) (M : ListAssignment (PathV (j + 1))) (c : ℕ) :
    (closePath (j + 1)).inducedList M c (pathEnd j) = (M (some (pathEnd j))).erase c := by
  rw [inducedList_closePath_succ]
  exact if_pos (Or.inl rfl)

/-- The list induced at the terminal vertex `pathStart j`: it too loses the color of the deleted
vertex. -/
lemma inducedList_closePath_pathStart (j : ℕ) (M : ListAssignment (PathV (j + 1))) (c : ℕ) :
    (closePath (j + 1)).inducedList M c (pathStart j) = (M (some (pathStart j))).erase c := by
  rw [inducedList_closePath_succ]
  exact if_pos (Or.inr rfl)

/-- Both terminal vertices of the path lose the color of the deleted vertex. -/
lemma inducedList_closePath_terminal (M : ListAssignment (PathV (j + 1))) (c : ℕ) {v : PathV j}
    (h : v = pathEnd j ∨ v = pathStart j) :
    (closePath (j + 1)).inducedList M c v = (M (some v)).erase c := by
  rw [inducedList_closePath_succ]
  exact if_pos h

/-- An interior vertex of the path keeps its whole list. -/
lemma inducedList_closePath_interior (M : ListAssignment (PathV (j + 1))) (c : ℕ)
    {v : PathV j} (h1 : v ≠ pathEnd j) (h2 : v ≠ pathStart j) :
    (closePath (j + 1)).inducedList M c v = M (some v) := by
  rw [inducedList_closePath_succ]
  exact if_neg (by tauto)

section Cards

variable {M : ListAssignment (PathV (j + 1))} (hM : IsNListAssignment M (m + 2)) (c : ℕ)
include hM

lemma card_inducedList_closePath_pathEnd :
    m + 1 ≤ ((closePath (j + 1)).inducedList M c (pathEnd j)).card := by
  rw [inducedList_closePath_pathEnd]
  have h1 : (M (some (pathEnd j))).card = m + 2 := hM _
  have h2 := Finset.pred_card_le_card_erase (s := M (some (pathEnd j))) (a := c)
  omega

lemma card_inducedList_closePath_pathStart :
    m + 1 ≤ ((closePath (j + 1)).inducedList M c (pathStart j)).card := by
  rw [inducedList_closePath_pathStart]
  have h1 : (M (some (pathStart j))).card = m + 2 := hM _
  have h2 := Finset.pred_card_le_card_erase (s := M (some (pathStart j))) (a := c)
  omega

lemma card_inducedList_closePath_interior :
    ∀ v : PathV j, v ≠ pathEnd j → v ≠ pathStart j →
      ((closePath (j + 1)).inducedList M c v).card = m + 2 := by
  intro v h1 h2
  rw [inducedList_closePath_interior M c h1 h2]
  exact hM _

end Cards

/-! ### Shrinking to an `(n, n-1)`-list assignment

The lists induced on `pathG j` by deleting a vertex of the cycle give `n` colors to every interior
vertex and `n` or `n - 1` colors to each terminal vertex. Cutting the terminal lists down to exactly
`n - 1` colors produces an honest `(n, n-1)`-assignment sitting inside them; the two subsets `Te`
and `Ts` below let one insist that a prescribed color survives the cut. -/

/-- **Shrinking to an `(n, n-1)`-assignment.** If `N` gives at least `n - 1` colors to each terminal
vertex of the path of length `j ≥ 1` and exactly `n` colors to each interior vertex, then there is
an `(n, n-1)`-list assignment `L` with `L v ⊆ N v` everywhere, equal to `N` off the two terminal
vertices, and containing prescribed subsets `Te`, `Ts` of size at most `n - 1` at the two ends. -/
lemma exists_isNNAssign_subset (hj : 1 ≤ j) {N : ListAssignment (PathV j)} {Te Ts : Finset ℕ}
    (hTe : Te ⊆ N (pathEnd j)) (hTec : Te.card ≤ m + 1)
    (hTs : Ts ⊆ N (pathStart j)) (hTsc : Ts.card ≤ m + 1)
    (hend : m + 1 ≤ (N (pathEnd j)).card) (hstart : m + 1 ≤ (N (pathStart j)).card)
    (hint : ∀ v, v ≠ pathEnd j → v ≠ pathStart j → (N v).card = m + 2) :
    ∃ L : ListAssignment (PathV j), (∀ v, L v ⊆ N v) ∧ IsNNAssign j m L ∧
      Te ⊆ L (pathEnd j) ∧ Ts ⊆ L (pathStart j) ∧
      ∀ v, v ≠ pathEnd j → v ≠ pathStart j → L v = N v := by
  have hne := pathEnd_ne_pathStart hj
  obtain ⟨E, hTeE, hEN, hEcard⟩ := Finset.exists_subsuperset_card_eq hTe hTec hend
  obtain ⟨S, hTsS, hSN, hScard⟩ := Finset.exists_subsuperset_card_eq hTs hTsc hstart
  refine ⟨fun v => if v = pathEnd j then E else if v = pathStart j then S else N v,
    ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro v
    dsimp only
    split_ifs with h1 h2
    · subst h1; exact hEN
    · subst h2; exact hSN
    · exact Finset.Subset.refl _
  · rw [if_pos rfl]
    exact hEcard
  · rw [if_neg (Ne.symm hne), if_pos rfl]
    exact hScard
  · intro v h1 h2
    rw [if_neg h1, if_neg h2]
    exact hint v h1 h2
  · dsimp only
    rw [if_pos rfl]
    exact hTeE
  · dsimp only
    rw [if_neg (Ne.symm hne), if_pos rfl]
    exact hTsS
  · intro v h1 h2
    dsimp only
    rw [if_neg h1, if_neg h2]

/-! ### The reduction of a cycle to a path -/

/-- **The reduction.** For every color `c` given to the deleted vertex of `closePath (j + 1)`, the
list assignment induced on the remaining path `pathG j` admits at least `min (A_j, B_j)` colorings.

This is the cycle half of Lemma 3(b): the induced assignment is not itself an
`(n, n-1)`-assignment — a terminal vertex keeps all `n` of its colors when `c` was not among them —
but it contains one, and `col` is monotone in the lists. -/
theorem min_pathA_pathB_le_col_inducedList (hj : 1 ≤ j)
    {M : ListAssignment (PathV (j + 1))} (hM : IsNListAssignment M (m + 2)) (c : ℕ) :
    min (pathA m j) (pathB m j)
      ≤ (pathG j).col ((closePath (j + 1)).inducedList M c) := by
  obtain ⟨L, hsub, hL, -, -, -⟩ :=
    exists_isNNAssign_subset (m := m) hj (Te := ∅) (Ts := ∅)
      (Finset.empty_subset _) (by simp) (Finset.empty_subset _) (by simp)
      (card_inducedList_closePath_pathEnd hM c) (card_inducedList_closePath_pathStart hM c)
      (card_inducedList_closePath_interior hM c)
  exact le_trans (min_pathA_pathB_le_col hL) (col_le_col_of_subset hsub)

/-! ### Case 1: an odd number of vertices -/

/-- **Case 1 of Theorem 1: cycles with an odd number of vertices are enumeratively
chromatic-choosable at `n`, for every `n ≥ 2`.**

`closePath (j + 1)` has `j + 2` vertices, so `Odd j` says the cycle has an odd number of vertices;
the smallest instance is `j = 1`, the triangle. No hypothesis on `n` is needed, and no hypothesis
that the list assignment is non-constant: each of the `n` terms of the fibrewise decomposition is
already at least `A_j`, because a path of *odd* length is worse off with a type A assignment. -/
theorem ecc_closePath_of_odd (hj : Odd j) (m : ℕ) :
    (closePath (j + 1)).ECCAt (m + 2) := by
  intro M hM
  have hj1 : 1 ≤ j := hj.pos
  have hmin : pathA m j = min (pathA m j) (pathB m j) :=
    (min_eq_left (pathA_lt_pathB hj m).le).symm
  rw [colConst_closePath_succ, col_closePath_succ]
  have hcard : (M (pathEnd (j + 1))).card = m + 2 := hM _
  calc (m + 2) * pathA m j
      = ∑ _c ∈ M (pathEnd (j + 1)), pathA m j := by
        rw [Finset.sum_const, hcard, smul_eq_mul]
    _ ≤ ∑ c ∈ M (pathEnd (j + 1)), (pathG j).col ((closePath (j + 1)).inducedList M c) :=
        Finset.sum_le_sum fun c _ => by
          rw [hmin]; exact min_pathA_pathB_le_col_inducedList hj1 hM c

/-! ### Case 2: an even number of vertices

For an even number of vertices the reduction only gives `n·B_j = n·A_j − n`, and the missing `n`
has to be recovered from the fine structure of the assignments that realize the minimum. The two
lemmas below are the two directions of that structure: an `(n, n-1)`-assignment on `pathG j` that is
*not* type B admits at least `A_j = B_j + 1` colorings, and conversely an assignment on `pathG j`
admitting fewer than `A_j` colorings *is* a type B `(n, n-1)`-assignment on the nose. -/

/-- For even `k` the type A count exceeds the type B count by exactly one; equation (5) of the
paper, read off in `ℕ`. -/
lemma pathA_eq_pathB_succ (hj : Even j) : pathA m j = pathB m j + 1 := by
  have h := pathA_sub_pathB m j
  rw [hj.neg_one_pow] at h
  omega

/-- **Not type B forces a strictly larger count.** Let `j ≥ 2` be even and `n = m + 2 ≥ 3`. If an
`(n, n-1)`-list assignment `L` on `pathG j` has, at one of its two terminal vertices, a color that
is missing from the interior list `L (pathVtx j 1)`, then `L` cannot be shaped (a shape has all its
terminal lists inside the common interior palette), hence cannot realize the minimum `B_j`, hence
admits at least `A_j = B_j + 1` colorings.

This is where Lemma 3(b) and the structure half of Lemma 3(c) are used. -/
theorem pathA_le_col_of_notMem_interior (hm : 1 ≤ m) (hj : 2 ≤ j) (hev : Even j)
    {L : ListAssignment (PathV j)} (hL : IsNNAssign j m L) {z : ℕ}
    (hz : z ∈ L (pathEnd j) ∨ z ∈ L (pathStart j)) (hz' : z ∉ L (pathVtx j 1)) :
    pathA m j ≤ (pathG j).col L := by
  have hmin : min (pathA m j) (pathB m j) = pathB m j := by
    rw [min_pathA_pathB_eq, if_pos hev]
  have hge : pathB m j ≤ (pathG j).col L := by
    rw [← hmin]; exact min_pathA_pathB_le_col hL
  have hAB : pathA m j = pathB m j + 1 := pathA_eq_pathB_succ hev
  rcases Nat.lt_or_ge (pathB m j) ((pathG j).col L) with h | h
  · omega
  · exfalso
    have heq : (pathG j).col L = pathB m j := le_antisymm h hge
    have hmini : (pathG j).Minimizing L := by
      intro L' hL'
      have hL'' : IsNNAssign j m L' :=
        ⟨by rw [hL' _]; exact hL.card_pathEnd, by rw [hL' _]; exact hL.card_pathStart,
          fun v ha hb => by rw [hL' v]; exact hL.card_interior v ha hb⟩
      rw [heq, ← hmin]
      exact min_pathA_pathB_le_col hL''
    obtain ⟨S, x, y, hshape⟩ := exists_isPathShape_of_minimizing hm hL hmini
    refine hz' ?_
    rw [hshape.apply_interior 1 (by omega) (by omega)]
    rcases hz with hz | hz
    · rw [hshape.apply_pathEnd] at hz; exact Finset.mem_of_mem_erase hz
    · rw [hshape.apply_pathStart] at hz; exact Finset.mem_of_mem_erase hz

/-- **Too few colorings forces a type B shape.** Let `j ≥ 2` be even and `n = m + 2 ≥ 3`. If `N`
gives at least `n - 1` colors to each terminal vertex of `pathG j`, exactly `n` colors to each
interior vertex, and admits fewer than `A_j` colorings, then `N` is *itself* an `(n, n-1)`-list
assignment, shaped by a palette `S` and two **distinct** missing colors — i.e. type B.

Both halves of the paper's argument are used: Lemma 4 (`ListColoring.col_lt_col_of_ssubset`)
rules out that `N` is strictly larger than the `(n, n-1)`-assignment inside it, and Lemma 3(c)
(`ListColoring.isPathShape_parity_of_minimizing`) supplies the type. -/
theorem isPathShape_of_col_lt (hm : 1 ≤ m) (hj : 2 ≤ j) (hev : Even j)
    {N : ListAssignment (PathV j)}
    (hend : m + 1 ≤ (N (pathEnd j)).card) (hstart : m + 1 ≤ (N (pathStart j)).card)
    (hint : ∀ v, v ≠ pathEnd j → v ≠ pathStart j → (N v).card = m + 2)
    (hlt : (pathG j).col N < pathA m j) :
    ∃ S x y, IsPathShape j m N S x y ∧ x ≠ y := by
  obtain ⟨L, hsub, hL, -, -, -⟩ :=
    exists_isNNAssign_subset (m := m) (by omega : 1 ≤ j) (Te := ∅) (Ts := ∅)
      (Finset.empty_subset _) (by simp) (Finset.empty_subset _) (by simp) hend hstart hint
  have hmin : min (pathA m j) (pathB m j) = pathB m j := by
    rw [min_pathA_pathB_eq, if_pos hev]
  have hAB : pathA m j = pathB m j + 1 := pathA_eq_pathB_succ hev
  have h1 : pathB m j ≤ (pathG j).col L := by rw [← hmin]; exact min_pathA_pathB_le_col hL
  have h2 : (pathG j).col L ≤ (pathG j).col N := col_le_col_of_subset hsub
  have hcard2 : ∀ v, 2 ≤ (N v).card := by
    intro v
    by_cases ha : v = pathEnd j
    · rw [ha]; omega
    by_cases hb : v = pathStart j
    · rw [hb]; omega
    · rw [hint v ha hb]; omega
  have hLN : L = N := by
    by_contra hne
    have := col_lt_col_of_ssubset j hsub hne hcard2
    omega
  rw [hLN] at hL h1
  have hcolN : (pathG j).col N = pathB m j := by omega
  have hmini : (pathG j).Minimizing N := by
    intro L' hL'
    have hL'' : IsNNAssign j m L' :=
      ⟨by rw [hL' _]; exact hL.card_pathEnd, by rw [hL' _]; exact hL.card_pathStart,
        fun v ha hb => by rw [hL' v]; exact hL.card_interior v ha hb⟩
    rw [hcolN, ← hmin]
    exact min_pathA_pathB_le_col hL''
  obtain ⟨S, x, y, hshape, hcase⟩ := isPathShape_parity_of_minimizing hm (by omega) hL hmini
  refine ⟨S, x, y, hshape, ?_⟩
  rcases hcase with ⟨hodd, -⟩ | ⟨-, hxy⟩
  · exact absurd hev (Nat.not_even_iff_odd.mpr hodd)
  · exact hxy

/-- The arithmetic of the paper's final display: `B + (A + 1) + (n − 2)·A = n·A` when
`A = B + 1`. -/
private lemma sum_lower_bound {T : Finset ℕ} {F : ℕ → ℕ} {A B c₀ d : ℕ}
    (hTcard : T.card = m + 2) (hAB : A = B + 1) (hB : B ≤ F c₀)
    (hc₀ : c₀ ∈ T) (hd : d ∈ T) (hne : d ≠ c₀)
    (hfd : A + 1 ≤ F d) (hrest : ∀ c ∈ T, c ≠ c₀ → A ≤ F c) :
    (m + 2) * A ≤ ∑ c ∈ T, F c := by
  have hd' : d ∈ T.erase c₀ := Finset.mem_erase.mpr ⟨hne, hd⟩
  have e1 : ∑ c ∈ T, F c = F c₀ + ∑ c ∈ T.erase c₀, F c := (Finset.add_sum_erase T F hc₀).symm
  have e2 : ∑ c ∈ T.erase c₀, F c = F d + ∑ c ∈ (T.erase c₀).erase d, F c :=
    (Finset.add_sum_erase _ F hd').symm
  have hcard1 : (T.erase c₀).card = m + 1 := by
    rw [Finset.card_erase_of_mem hc₀, hTcard]
    omega
  have hcard0 : ((T.erase c₀).erase d).card = m := by
    rw [Finset.card_erase_of_mem hd', hcard1]
    omega
  have e3 : m * A ≤ ∑ c ∈ (T.erase c₀).erase d, F c := by
    calc m * A = ∑ _c ∈ (T.erase c₀).erase d, A := by
          rw [Finset.sum_const, hcard0, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun c hc =>
          hrest c (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc))
  have key : (m + 2) * A = B + ((A + 1) + m * A) := by rw [hAB]; ring
  rw [e1, e2, key]
  omega

/-- **Case 2 of Theorem 1: cycles with an even number of vertices are enumeratively
chromatic-choosable at `n`, for every `n ≥ 3`.**

`closePath (j + 1)` has `j + 2` vertices, so `Even j` says the cycle has an even number of vertices;
`2 ≤ j` excludes the degenerate `closePath 1`, a single edge. The hypothesis `1 ≤ m`, i.e. `n ≥ 3`,
is genuinely needed here: Lemma 3(c) — and with it this whole argument — fails at `n = 2`, which the
paper handles by a separate argument that is not formalized. -/
theorem ecc_closePath_of_even (hj : 2 ≤ j) (hev : Even j) (hm : 1 ≤ m) :
    (closePath (j + 1)).ECCAt (m + 2) := by
  intro M hM
  have hj1 : 1 ≤ j := by omega
  have hAB : pathA m j = pathB m j + 1 := pathA_eq_pathB_succ hev
  have hTcard : (M (pathEnd (j + 1))).card = m + 2 := hM _
  have hx1e : pathVtx j 1 ≠ pathEnd j := pathVtx_ne_pathEnd (by omega) (by omega)
  have hx1s : pathVtx j 1 ≠ pathStart j := pathVtx_ne_pathStart (by omega)
  rw [colConst_closePath_succ, col_closePath_succ]
  by_cases hall : ∀ c ∈ M (pathEnd (j + 1)),
      pathA m j ≤ (pathG j).col ((closePath (j + 1)).inducedList M c)
  · -- every fibre already reaches `A_j`
    calc (m + 2) * pathA m j
        = ∑ _c ∈ M (pathEnd (j + 1)), pathA m j := by
          rw [Finset.sum_const, hTcard, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hall
  -- some fibre falls short; it is then a type B shape, and pins down all the others
  obtain ⟨c₀, hc₀T, hc₀lt⟩ : ∃ c ∈ M (pathEnd (j + 1)),
      (pathG j).col ((closePath (j + 1)).inducedList M c) < pathA m j := by
    by_contra hcon
    exact hall fun c hc => Nat.le_of_not_lt fun h => hcon ⟨c, hc, h⟩
  obtain ⟨S, p, q, hshape, hpq⟩ := isPathShape_of_col_lt hm hj hev
    (card_inducedList_closePath_pathEnd hM c₀) (card_inducedList_closePath_pathStart hM c₀)
    (card_inducedList_closePath_interior hM c₀) hc₀lt
  -- the palette of the shape is the common interior list of `M`
  have hSeq : M (some (pathVtx j 1)) = S := by
    rw [← inducedList_closePath_interior M c₀ hx1e hx1s]
    exact hshape.apply_interior 1 (by omega) (by omega)
  have hEeq : (M (some (pathEnd j))).erase c₀ = S.erase p := by
    rw [← inducedList_closePath_pathEnd j M c₀]; exact hshape.apply_pathEnd
  have hSSeq : (M (some (pathStart j))).erase c₀ = S.erase q := by
    rw [← inducedList_closePath_pathStart j M c₀]; exact hshape.apply_pathStart
  have hScard : (S.erase p).card = m + 1 := by
    rw [Finset.card_erase_of_mem hshape.mem_left, hshape.card_palette]
    omega
  have hScard' : (S.erase q).card = m + 1 := by
    rw [Finset.card_erase_of_mem hshape.mem_right, hshape.card_palette]
    omega
  -- `c₀` really was removed at both ends, so it lay in both terminal lists of `M`
  have hc₀u : c₀ ∈ M (some (pathEnd j)) := by
    by_contra hcon
    rw [Finset.erase_eq_of_notMem hcon] at hEeq
    have h1 : (M (some (pathEnd j))).card = m + 2 := hM _
    rw [hEeq, hScard] at h1
    omega
  have hc₀w : c₀ ∈ M (some (pathStart j)) := by
    by_contra hcon
    rw [Finset.erase_eq_of_notMem hcon] at hSSeq
    have h1 : (M (some (pathStart j))).card = m + 2 := hM _
    rw [hSSeq, hScard'] at h1
    omega
  -- but `c₀` is not in the palette: it would have to be both missing colors at once
  have hc₀S : c₀ ∉ S := by
    intro hin
    have hnp : c₀ ∉ S.erase p := by rw [← hEeq]; exact Finset.notMem_erase _ _
    have hnq : c₀ ∉ S.erase q := by rw [← hSSeq]; exact Finset.notMem_erase _ _
    have hp : c₀ = p := by by_contra h; exact hnp (Finset.mem_erase.mpr ⟨h, hin⟩)
    have hq : c₀ = q := by by_contra h; exact hnq (Finset.mem_erase.mpr ⟨h, hin⟩)
    exact hpq (hp.symm.trans hq)
  -- the two neighbors of the deleted vertex have different lists, so one differs from its own
  have huw : M (some (pathEnd j)) ≠ M (some (pathStart j)) := by
    intro heq
    refine hpq (eq_of_erase_eq_erase hshape.mem_right ?_)
    rw [← hEeq, ← hSSeq, heq]
  obtain ⟨w', hw'mem, hw'ne, hc₀w'⟩ :
      ∃ w' : PathV j, (w' = pathEnd j ∨ w' = pathStart j) ∧
        M (pathEnd (j + 1)) ≠ M (some w') ∧ c₀ ∈ M (some w') := by
    by_cases h : M (pathEnd (j + 1)) = M (some (pathEnd j))
    · exact ⟨pathStart j, Or.inr rfl, fun hcon => huw (h.symm.trans hcon), hc₀w⟩
    · exact ⟨pathEnd j, Or.inl rfl, h, hc₀u⟩
  obtain ⟨d, hdT, hdnot⟩ : ∃ d ∈ M (pathEnd (j + 1)), d ∉ M (some w') := by
    by_contra hcon
    refine hw'ne (Finset.eq_of_subset_of_card_le (fun z hz => ?_) (by rw [hM _, hM _]))
    by_contra hz'
    exact hcon ⟨z, hz, hz'⟩
  have hdne : d ≠ c₀ := fun h => hdnot (by rw [h]; exact hc₀w')
  -- the colorings that avoid `c₀` at the deleted vertex: at least `A_j` each
  have hrest : ∀ c, c ≠ c₀ →
      pathA m j ≤ (pathG j).col ((closePath (j + 1)).inducedList M c) := by
    intro c hcne
    have hmemE : c₀ ∈ (closePath (j + 1)).inducedList M c (pathEnd j) := by
      rw [inducedList_closePath_pathEnd]
      exact Finset.mem_erase.mpr ⟨Ne.symm hcne, hc₀u⟩
    have hmemS : c₀ ∈ (closePath (j + 1)).inducedList M c (pathStart j) := by
      rw [inducedList_closePath_pathStart]
      exact Finset.mem_erase.mpr ⟨Ne.symm hcne, hc₀w⟩
    obtain ⟨L, hsub, hL, hTe, -, hLint⟩ :=
      exists_isNNAssign_subset (m := m) hj1 (Te := {c₀}) (Ts := {c₀})
        (Finset.singleton_subset_iff.mpr hmemE) (by simp)
        (Finset.singleton_subset_iff.mpr hmemS) (by simp)
        (card_inducedList_closePath_pathEnd hM c) (card_inducedList_closePath_pathStart hM c)
        (card_inducedList_closePath_interior hM c)
    have hzL : c₀ ∈ L (pathEnd j) := Finset.singleton_subset_iff.mp hTe
    have hzL' : c₀ ∉ L (pathVtx j 1) := by
      rw [hLint _ hx1e hx1s, inducedList_closePath_interior M c hx1e hx1s, hSeq]
      exact hc₀S
    exact le_trans (pathA_le_col_of_notMem_interior hm hj hev hL (Or.inl hzL) hzL')
      (col_le_col_of_subset hsub)
  -- the colorings that give `d` to the deleted vertex: at least `A_j + 1`
  have hfd : pathA m j + 1 ≤ (pathG j).col ((closePath (j + 1)).inducedList M d) := by
    have hmemE : c₀ ∈ (closePath (j + 1)).inducedList M d (pathEnd j) := by
      rw [inducedList_closePath_pathEnd]
      exact Finset.mem_erase.mpr ⟨Ne.symm hdne, hc₀u⟩
    have hmemS : c₀ ∈ (closePath (j + 1)).inducedList M d (pathStart j) := by
      rw [inducedList_closePath_pathStart]
      exact Finset.mem_erase.mpr ⟨Ne.symm hdne, hc₀w⟩
    obtain ⟨L, hsub, hL, hTe, -, hLint⟩ :=
      exists_isNNAssign_subset (m := m) hj1 (Te := {c₀}) (Ts := {c₀})
        (Finset.singleton_subset_iff.mpr hmemE) (by simp)
        (Finset.singleton_subset_iff.mpr hmemS) (by simp)
        (card_inducedList_closePath_pathEnd hM d) (card_inducedList_closePath_pathStart hM d)
        (card_inducedList_closePath_interior hM d)
    have hzL : c₀ ∈ L (pathEnd j) := Finset.singleton_subset_iff.mp hTe
    have hzL' : c₀ ∉ L (pathVtx j 1) := by
      rw [hLint _ hx1e hx1s, inducedList_closePath_interior M d hx1e hx1s, hSeq]
      exact hc₀S
    have hA := pathA_le_col_of_notMem_interior hm hj hev hL (Or.inl hzL) hzL'
    -- `d` was not available at `w'` in the first place, so nothing was erased there
    have hval : (closePath (j + 1)).inducedList M d w' = M (some w') := by
      rw [inducedList_closePath_terminal M d hw'mem, Finset.erase_eq_of_notMem hdnot]
    have hNw' : ((closePath (j + 1)).inducedList M d w').card = m + 2 := by
      rw [hval]; exact hM _
    have hLw' : (L w').card = m + 1 := by
      rcases hw'mem with h | h
      · rw [h]; exact hL.card_pathEnd
      · rw [h]; exact hL.card_pathStart
    have hstrict : L ≠ (closePath (j + 1)).inducedList M d := by
      intro hEq
      rw [hEq, hNw'] at hLw'
      omega
    have hcard2 : ∀ v, 2 ≤ ((closePath (j + 1)).inducedList M d v).card := by
      intro v
      by_cases ha : v = pathEnd j
      · have h := card_inducedList_closePath_pathEnd (m := m) hM d
        rw [ha]; omega
      by_cases hb : v = pathStart j
      · have h := card_inducedList_closePath_pathStart (m := m) hM d
        rw [hb]; omega
      · rw [card_inducedList_closePath_interior hM d v ha hb]; omega
    have hlt := col_lt_col_of_ssubset j hsub hstrict hcard2
    omega
  -- and the fibre of `c₀` itself is at least `B_j`
  have hBc₀ : pathB m j ≤ (pathG j).col ((closePath (j + 1)).inducedList M c₀) := by
    have h := min_pathA_pathB_le_col_inducedList hj1 hM c₀
    rw [min_pathA_pathB_eq, if_pos hev] at h
    exact h
  exact sum_lower_bound (m := m)
    (F := fun c => (pathG j).col ((closePath (j + 1)).inducedList M c))
    hTcard hAB hBc₀ hc₀T hdT hdne hfd fun c _ hc => hrest c hc

/-! ### Theorem 1 -/

/-- **Theorem 1 of Kirov–Naimi, for `n ≥ 3`: every cycle is enumeratively chromatic-choosable at
`n`.**

`closePath (j + 1)` is the cycle on `j + 2` vertices, so `1 ≤ j` says exactly that it is a cycle
(and not the degenerate `closePath 1`, a single edge). For `n = 2` only the odd case is available
here; see `ListColoring.ecc_closePath_of_odd`. -/
theorem ecc_closePath_succ (hj : 1 ≤ j) (hm : 1 ≤ m) :
    (closePath (j + 1)).ECCAt (m + 2) := by
  rcases Nat.even_or_odd j with hev | hodd
  · exact ecc_closePath_of_even (by rcases hev with ⟨r, hr⟩; omega) hev hm
  · exact ecc_closePath_of_odd hodd m

/-- **Theorem 1 of Kirov–Naimi, for `n ≥ 3`**, indexed as in `ListColoring.colConst_closePath`:
`closePath k` is the cycle on `k + 1` vertices, and `2 ≤ k` says it has at least three. -/
theorem ecc_closePath {k : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) :
    (closePath k).ECCAt (m + 2) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  exact ecc_closePath_succ (by omega) hm

end ListColoring
