/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.CycleRotate
import Monophilic.Core

/-!
# The list color function of a cycle

This file states Theorem 1 of Kirov–Naimi in the form the literature usually writes it: the **list
color function** of a cycle agrees with its chromatic polynomial.

For a graph `G`, the list color function `P_ℓ(G, n)` is the *minimum* of `col(G, L)` over all
`n`-list assignments `L`, and `P(G, n)` is the number of proper colorings from a single palette of
`n` colors. Saying `G` is `n`-monophilic is exactly saying that this minimum is attained at the
constant assignment, i.e. `P_ℓ(G, n) = P(G, n)`.

## Main results

* `Monophilic.monophilic_closePath_all` : every cycle is `n`-monophilic for **every** `n`, with no
  hypothesis on `n` whatsoever
* `Monophilic.isLeast_col_closePath` : `P_ℓ(C, n) = P(C, n)`, stated as `IsLeast` — the constant
  assignment is achievable and no `n`-list assignment does better
* `Monophilic.colConst_closePath_chromatic` : `P(C_v, n) = (n-1)^v + (-1)^v (n-1)`, the classical
  chromatic polynomial of a cycle, so the right-hand side above is explicit

## A caveat on the word "polynomial"

This development never constructs the chromatic polynomial as an element of `Polynomial ℤ`; it works
throughout with the *count* `colConst G n`, which is that polynomial's value at `n`. Nothing in
Kirov–Naimi needs the polynomial itself, and avoiding it removes deletion–contraction and edge
contraction from the critical path. `colConst_closePath_chromatic` below is what ties the count to
the familiar closed form.
-/

namespace Monophilic

open SimpleGraph

/-- **Every cycle is `n`-monophilic, for every `n`.** `closePath k` is the cycle on `k + 1`
vertices, so `2 ≤ k` says only that it really is a cycle — there is no hypothesis on `n` at all.

For `n ≥ 2` this is Theorem 1 (`monophilic_closePath_of_two_le`); for `n ≤ 1` it is
`SimpleGraph.monophilic_of_le_one`, which holds for any graph. -/
theorem monophilic_closePath_all (k n : ℕ) (hk : 2 ≤ k) : (closePath k).Monophilic n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · exact monophilic_of_le_one (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    exact monophilic_closePath_of_two_le hk

/-- **`P_ℓ(C, n) = P(C, n)`.** The number of colorings from the constant palette is the *least*
achievable over all `n`-list assignments — and it is achieved, by the constant assignment itself.
That is precisely the assertion that the list color function of a cycle agrees with its chromatic
polynomial at every `n`. -/
theorem isLeast_col_closePath (k n : ℕ) (hk : 2 ≤ k) :
    IsLeast {c | ∃ L : ListAssignment (PathV k), IsNListAssignment L n ∧ (closePath k).col L = c}
      ((closePath k).colConst n) := by
  constructor
  · exact ⟨constList (PathV k) n, isNListAssignment_constList n, rfl⟩
  · rintro c ⟨L, hL, rfl⟩
    exact monophilic_closePath_all k n hk L hL

/-- **The chromatic polynomial of a cycle, as a closed form.** `closePath (k+1)` is the cycle on
`v = k + 2` vertices, and its coloring count from a palette of `n = m + 2` colors is
`(n-1)^v + (-1)^v (n-1)`.

Combined with `isLeast_col_closePath` this makes the right-hand side of `P_ℓ = P` explicit: for a
cycle on `v` vertices, the least number of list colorings over all `n`-list assignments is exactly
`(n-1)^v + (-1)^v (n-1)`. -/
theorem colConst_closePath_chromatic (m k : ℕ) :
    (((closePath (k + 1)).colConst (m + 2) : ℤ))
      = ((m + 1) : ℤ) ^ (k + 2) + (-1) ^ (k + 2) * ((m + 1) : ℤ) := by
  have h := colConst_closePath_succ m k
  have hA := pathA_closed_form m k
  have hcast : (((closePath (k + 1)).colConst (m + 2) : ℕ) : ℤ) = ((m + 2) * pathA m k : ℕ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
  rw [hcast]; push_cast; rw [hA]; ring_nf

/-! ### Sanity checks against the classical formula -/

#guard (closePath 2).colConst 3 = 6      -- C₃ with 3 colours: 2^3 - 2
#guard (closePath 3).colConst 3 = 18     -- C₄: 2^4 + 2
#guard (closePath 4).colConst 3 = 30     -- C₅: 2^5 - 2
#guard (closePath 5).colConst 3 = 66     -- C₆: 2^6 + 2
#guard (closePath 3).colConst 4 = 84     -- C₄ with 4 colours: 3^4 + 3

end Monophilic
