/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring.CycleRotate
import ListColoring.Core
import ListColoring.ChromaticPolynomial

/-!
# The list color function

For a graph `G`, the **list color function** `P_ℓ(G, n)` is the *minimum* of `col(G, L)` over all
`n`-list assignments `L`, and `P(G, n)` is the number of proper colorings from a single palette of
`n` colors. Kostochka and Sidorenko's question, and the whole subject of Kirov–Naimi, is when the
two agree.

This file defines `P_ℓ` for an arbitrary graph and shows that the paper's enumerative
chromatic-choosability at `n` is *exactly* the statement `P_ℓ(G, n) = P(G, n)`. Everything here is
general; the cycle results at the end are corollaries of Theorem 1.

## Main results

* `SimpleGraph.listColorFunction G n` : `P_ℓ(G, n)`
* `SimpleGraph.ecc_iff_listColorFunction_eq` : `G` is enumeratively chromatic-choosable at `n`
  **iff** `P_ℓ(G, n) = P(G, n)` — the two formulations coincide, for every graph and every `n`
* `ListColoring.ecc_closePath_all`, `ListColoring.closePath_ecc` : **Theorem 1 with no hypothesis
  on `n`** — every cycle is enumeratively chromatic-choosable, pointwise and bundled
* `ListColoring.listColorFunction_closePath` : for a cycle, `P_ℓ(C, n) = P(C, n)` for every `n`
* `ListColoring.colConst_closePath_chromatic` : and that common value is
  `(n-1)^v + (-1)^v (n-1)`, the classical chromatic polynomial of a cycle on `v` vertices

## On the word "polynomial"

`P(G, n)` here is the *count* `colConst G n`. The chromatic polynomial proper — an element of
`Polynomial ℤ` whose evaluation is this count — is built separately in
`ListColoring.ChromaticPolynomial`, via the Whitney subset expansion rather than
deletion–contraction, since Mathlib has no edge contraction. Nothing in Kirov–Naimi needs the
polynomial itself, which is why the development did without it for so long.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The set of coloring counts achievable by `n`-list assignments. -/
def colCounts (n : ℕ) : Set ℕ := {c | ∃ L : ListAssignment V, IsNListAssignment L n ∧ G.col L = c}

lemma colConst_mem_colCounts (n : ℕ) : G.colConst n ∈ G.colCounts n :=
  ⟨constList V n, isNListAssignment_constList n, rfl⟩

lemma colCounts_nonempty (n : ℕ) : (G.colCounts n).Nonempty :=
  ⟨_, G.colConst_mem_colCounts n⟩

/-- **The list color function** `P_ℓ(G, n)`: the least number of colorings achievable by any
`n`-list assignment. -/
noncomputable def listColorFunction (n : ℕ) : ℕ := sInf (G.colCounts n)

variable {G}

/-- `P_ℓ` really is achieved by some `n`-list assignment — the infimum is a minimum. -/
lemma listColorFunction_mem (n : ℕ) : G.listColorFunction n ∈ G.colCounts n :=
  Nat.sInf_mem (G.colCounts_nonempty n)

/-- `P_ℓ(G, n)` is a lower bound for every `n`-list assignment. -/
theorem listColorFunction_le_col {n : ℕ} {L : ListAssignment V} (hL : IsNListAssignment L n) :
    G.listColorFunction n ≤ G.col L :=
  Nat.sInf_le ⟨L, hL, rfl⟩

/-- `P_ℓ(G, n) ≤ P(G, n)`, always: the constant assignment is one of the candidates. -/
theorem listColorFunction_le_colConst (n : ℕ) : G.listColorFunction n ≤ G.colConst n :=
  Nat.sInf_le (G.colConst_mem_colCounts n)

/-- **enumerative chromatic-choosability at `n` is exactly `P_ℓ(G, n) = P(G, n)`.**

This is the bridge between the paper's formulation and the way the literature usually writes the
question. `G` is enumeratively chromatic-choosable at `n` when the constant list assignment
minimizes the number of colorings; that says precisely that the minimum defining `P_ℓ` is
attained there, i.e. that the list color function agrees with the chromatic polynomial at `n`. -/
theorem ecc_iff_listColorFunction_eq (n : ℕ) :
    G.ECCAt n ↔ G.listColorFunction n = G.colConst n := by
  constructor
  · intro hmono
    refine le_antisymm (listColorFunction_le_colConst n) ?_
    obtain ⟨L, hL, hcol⟩ := listColorFunction_mem (G := G) n
    exact hcol ▸ hmono L hL
  · intro heq L hL
    exact heq ▸ listColorFunction_le_col hL

/-- **`P_ℓ(G, n) = P(G, n)` with a genuine polynomial on the right.**

`ListColoring.ChromaticPolynomial` builds `chromaticPolynomial G : Polynomial ℤ` by the Whitney
subset expansion, and `eval_chromaticPolynomial` says its value at `n` is the coloring count. So
enumerative chromatic-choosability at `n` is literally the assertion that the list color function
agrees with the chromatic polynomial at `n` — for an arbitrary graph. -/
theorem ecc_iff_listColorFunction_eq_eval (n : ℕ) :
    G.ECCAt n ↔ (G.listColorFunction n : ℤ) = (G.chromaticPolynomial).eval (n : ℤ) := by
  rw [ecc_iff_listColorFunction_eq, eval_chromaticPolynomial]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

end SimpleGraph

namespace ListColoring

open SimpleGraph

/-- **Every cycle is enumeratively chromatic-choosable at `n`, for every `n`.** `closePath k` is the
cycle on `k + 1` vertices, so `2 ≤ k` says only that it really is a cycle — there is no hypothesis
on `n` at all.

For `n ≥ 2` this is Theorem 1 (`ecc_closePath_of_two_le`); for `n ≤ 1` it is
`SimpleGraph.ecc_of_le_one`, which holds for any graph. -/
theorem ecc_closePath_all (k n : ℕ) (hk : 2 ≤ k) : (closePath k).ECCAt n := by
  rcases Nat.lt_or_ge n 2 with h | h
  · exact ecc_of_le_one (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    exact ecc_closePath_of_two_le hk

/-- **Every cycle is enumeratively chromatic-choosable**, in the bundled `SimpleGraph.ECC` form.
This is Theorem 1 of Kirov–Naimi with the quantifier over `n` absorbed into the predicate;
`closePath k` is the cycle on `k + 1` vertices, so `2 ≤ k` says only that it really is a cycle. -/
theorem closePath_ecc (k : ℕ) (hk : 2 ≤ k) : (closePath k).ECC :=
  fun n => ecc_closePath_all k n hk

/-- **`P_ℓ(C, n) = P(C, n)` for every cycle and every `n`** — Theorem 1 of Kirov–Naimi, in the
notation the literature uses. -/
theorem listColorFunction_closePath (k n : ℕ) (hk : 2 ≤ k) :
    (closePath k).listColorFunction n = (closePath k).colConst n :=
  (ecc_iff_listColorFunction_eq n).mp (ecc_closePath_all k n hk)

/-- **The chromatic polynomial of a cycle, as a closed form.** `closePath (k+1)` is the cycle on
`v = k + 2` vertices, and its coloring count from a palette of `n = m + 2` colors is
`(n-1)^v + (-1)^v (n-1)`.

Combined with `listColorFunction_closePath` this makes the common value explicit: for a cycle on `v`
vertices, the least number of list colorings over all `n`-list assignments is exactly
`(n-1)^v + (-1)^v (n-1)`. -/
theorem colConst_closePath_chromatic (m k : ℕ) :
    (((closePath (k + 1)).colConst (m + 2) : ℤ))
      = ((m + 1) : ℤ) ^ (k + 2) + (-1) ^ (k + 2) * ((m + 1) : ℤ) := by
  have h := colConst_closePath_succ m k
  have hA := pathA_closed_form m k
  have hcast : (((closePath (k + 1)).colConst (m + 2) : ℕ) : ℤ) = ((m + 2) * pathA m k : ℕ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) h
  rw [hcast]; push_cast; rw [hA]; ring_nf

/-- The two together: for a cycle on `v = k + 2` vertices and `n = m + 2` colors, the list color
function is exactly `(n-1)^v + (-1)^v (n-1)`.

The hypothesis `1 ≤ k` is what makes `closePath (k+1)` an actual cycle: at `k = 0` it is
`closePath 1`, a single edge on two vertices. (The closed form in
`colConst_closePath_chromatic` does hold there too — `(n-1)^2 + (n-1) = n(n-1)` is the right count
for an edge — but `listColorFunction_closePath` is stated for genuine cycles.) -/
theorem listColorFunction_closePath_chromatic (m k : ℕ) (hk : 1 ≤ k) :
    (((closePath (k + 1)).listColorFunction (m + 2) : ℤ))
      = ((m + 1) : ℤ) ^ (k + 2) + (-1) ^ (k + 2) * ((m + 1) : ℤ) := by
  rw [listColorFunction_closePath (k + 1) (m + 2) (by omega)]
  exact colConst_closePath_chromatic m k

/-! ### Sanity checks against the classical formula -/

#guard (closePath 2).colConst 3 = 6      -- C₃ with 3 colours: 2^3 - 2
#guard (closePath 3).colConst 3 = 18     -- C₄: 2^4 + 2
#guard (closePath 4).colConst 3 = 30     -- C₅: 2^5 - 2
#guard (closePath 5).colConst 3 = 66     -- C₆: 2^6 + 2
#guard (closePath 3).colConst 4 = 84     -- C₄ with 4 colours: 3^4 + 3

end ListColoring
