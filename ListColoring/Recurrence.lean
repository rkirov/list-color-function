/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# The arithmetic core of Lemma 3 of Kirov–Naimi

This file isolates the purely arithmetic content of Lemma 3 of R. Kirov and R. Naimi,
*List coloring and n-monophilic graphs*. No graph theory appears here.

In the paper, `A_k` and `B_k` count the colorings of a path of length `k` coming from a
"type A" resp. "type B" `(n, n-1)`-list assignment, and they satisfy the mutual recurrence

* `A_k = (n-1) * B_{k-1}`,
* `B_k = A_{k-1} + (n-2) * B_{k-1}`,

with initial values `A_0 = n - 1` and `B_0 = n - 2`.

Throughout we write `n = m + 2`, so that `n - 1 = m + 1` and `n - 2 = m` are honest natural
numbers and no truncated subtraction occurs. The two sequences are `pathA m` and `pathB m`.

## Main results

* `pathA_sub_pathB`: the paper's equation (5), `A_k - B_k = (-1) ^ k` (as an identity in `ℤ`).
* `pathA_closed_form`: the paper's `A_k = ((n-1)/n) * ((n-1)^(k+1) + (-1)^k)`, cleared of the
  division: `(m + 2) * A_k = (m + 1) * ((m + 1) ^ (k + 1) + (-1) ^ k)`.
* `pathB_closed_form`: the companion formula `(m + 2) * B_k = (m + 1) ^ (k + 2) - (-1) ^ k`.
* `pathB_lt_pathA` / `pathA_lt_pathB`: `B_k < A_k` for even `k`, and `A_k < B_k` for odd `k`.
* `min_pathA_pathB_eq`: consequently `min A_k B_k = if Even k then B_k else A_k`.

## Implementation notes

`pathA` and `pathB` are defined by a genuine `mutual` structural recursion. The four defining
equations are additionally recorded as the `@[simp]` lemmas `pathA_zero`, `pathB_zero`,
`pathA_succ`, `pathB_succ`, so that downstream files can rewrite with them without relying on
the shape of the equation compiler's output.

All the identities are stated over `ℤ`, since `A_k - B_k` is negative for odd `k` and natural
subtraction would truncate it.  The order comparisons, by contrast, are stated over `ℕ`, where
they will be used; they are transferred from the `ℤ` identity by `exact_mod_cast`.
-/

namespace ListColoring

mutual

/-- Paper's `A_k` for `n = m + 2`: the number of colorings of a path of length `k`
coming from a type A list assignment.  The recurrence is `A_0 = n - 1 = m + 1` and
`A_{k+1} = (n - 1) * B_k = (m + 1) * B_k`. -/
def pathA (m : ℕ) : ℕ → ℕ
  | 0 => m + 1
  | k + 1 => (m + 1) * pathB m k

/-- Paper's `B_k` for `n = m + 2`: the number of colorings of a path of length `k`
coming from a type B list assignment.  The recurrence is `B_0 = n - 2 = m` and
`B_{k+1} = A_k + (n - 2) * B_k = A_k + m * B_k`. -/
def pathB (m : ℕ) : ℕ → ℕ
  | 0 => m
  | k + 1 => pathA m k + m * pathB m k

end

/-- Defining equation: `A_0 = n - 1 = m + 1`. -/
@[simp] theorem pathA_zero (m : ℕ) : pathA m 0 = m + 1 := by
  rw [pathA]

/-- Defining equation: `B_0 = n - 2 = m`. -/
@[simp] theorem pathB_zero (m : ℕ) : pathB m 0 = m := by
  rw [pathB]

/-- Defining equation: `A_{k+1} = (n - 1) * B_k = (m + 1) * B_k`. -/
@[simp] theorem pathA_succ (m k : ℕ) : pathA m (k + 1) = (m + 1) * pathB m k := by
  rw [pathA]

/-- Defining equation: `B_{k+1} = A_k + (n - 2) * B_k = A_k + m * B_k`. -/
@[simp] theorem pathB_succ (m k : ℕ) : pathB m (k + 1) = pathA m k + m * pathB m k := by
  rw [pathB]

/-- Equation (5) of the paper: `A_k - B_k = (-1) ^ k`, as an identity in `ℤ`.

Note that the subtraction genuinely needs to happen in `ℤ`: for odd `k` we have `A_k < B_k`. -/
theorem pathA_sub_pathB (m k : ℕ) : ((pathA m k : ℤ) - (pathB m k : ℤ)) = (-1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pathA_succ, pathB_succ]
    push_cast
    linear_combination -ih

/-- `A_k = B_k + (-1) ^ k` in `ℤ`; a restatement of `pathA_sub_pathB`. -/
theorem pathA_eq_pathB_add (m k : ℕ) : (pathA m k : ℤ) = (pathB m k : ℤ) + (-1) ^ k := by
  linarith [pathA_sub_pathB m k]

/-- Closed form for `B_k`: `n * B_k = (n - 1) ^ (k + 2) - (-1) ^ k` with `n = m + 2`.

This is the companion to `pathA_closed_form`.  We prove this one first, by induction on `k`
(using equation (5) to eliminate `A_k` from the recurrence for `B_{k+1}`), and then read off
`pathA_closed_form` from it, again via equation (5). -/
theorem pathB_closed_form (m k : ℕ) :
    ((m + 2) * pathB m k : ℤ) = (m + 1) ^ (k + 2) - (-1) ^ k := by
  induction k with
  | zero => simp only [pathB_zero]; push_cast; ring
  | succ k ih =>
    have hAB : (pathA m k : ℤ) = (pathB m k : ℤ) + (-1) ^ k := pathA_eq_pathB_add m k
    rw [pathB_succ]
    push_cast
    rw [hAB]
    linear_combination ((m : ℤ) + 1) * ih

/-- Closed form for `A_k`, i.e. the paper's `A_k = ((n-1)/n) * ((n-1) ^ (k+1) + (-1) ^ k)`
with `n = m + 2`, cleared of the division:
`(m + 2) * A_k = (m + 1) * ((m + 1) ^ (k + 1) + (-1) ^ k)`. -/
theorem pathA_closed_form (m k : ℕ) :
    ((m + 2) * pathA m k : ℤ) = (m + 1) * ((m + 1) ^ (k + 1) + (-1) ^ k) := by
  have hB := pathB_closed_form m k
  have hAB : (pathA m k : ℤ) = (pathB m k : ℤ) + (-1) ^ k := pathA_eq_pathB_add m k
  rw [hAB]
  linear_combination hB

/-- For even `k` the type B count is strictly smaller: `B_k < A_k`. -/
theorem pathB_lt_pathA {k : ℕ} (hk : Even k) (m : ℕ) : pathB m k < pathA m k := by
  have h := pathA_sub_pathB m k
  rw [hk.neg_one_pow] at h
  have : (pathB m k : ℤ) < (pathA m k : ℤ) := by linarith
  exact_mod_cast this

/-- For odd `k` the type A count is strictly smaller: `A_k < B_k`. -/
theorem pathA_lt_pathB {k : ℕ} (hk : Odd k) (m : ℕ) : pathA m k < pathB m k := by
  have h := pathA_sub_pathB m k
  rw [hk.neg_one_pow] at h
  have : (pathA m k : ℤ) < (pathB m k : ℤ) := by linarith
  exact_mod_cast this

/-- The minimum of `A_k` and `B_k`, as used in the paper to identify which of the two
list-assignment types realises the fewest colorings: it is `B_k` for even `k` and `A_k`
for odd `k`. -/
theorem min_pathA_pathB_eq (m k : ℕ) :
    min (pathA m k) (pathB m k) = if Even k then pathB m k else pathA m k := by
  by_cases hk : Even k
  · rw [if_pos hk]
    exact min_eq_right (pathB_lt_pathA hk m).le
  · rw [if_neg hk]
    exact min_eq_left (pathA_lt_pathB (Nat.not_even_iff_odd.mp hk) m).le

end ListColoring
