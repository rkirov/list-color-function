/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import ListColoring

/-!
# The questions Kirov–Naimi leave open

Section 6 of **Kirov–Naimi 2016** poses two questions. Both are still open. This file states them
in Lean and asserts them with `sorry`, so that the statements are elaborated and type-checked on
every build even though nothing here is proved.

## Read the `sorry`s correctly

A `sorry` in this file means **nobody knows**, not "we did not get to it". These are not gaps in
the formalization of the paper; they are the paper's own open questions, and each is stated in the
direction the paper conjectures. A refutation would be just as good an answer, so proving the
negation of one of these is not a contradiction with anything asserted here.

**Nothing in `ListColoring/` may depend on this file.** The dependency runs one way — this library
imports `ListColoring`, never the reverse — and `ListColoring/` remains free of `sorry`, `admit`
and `native_decide`, which CI checks by `grep` over that directory. That separation is the whole
reason these live in their own library rather than beside the theorems they are about.

## What is here

* `Question1` / `question1` — is the Cartesian product of two `n`-monophilic graphs `n`-monophilic,
  for `n ≥ 3`? The paper's "product" is `V(G) × V(H)` with `(g,h)` adjacent to `(g',h')` when
  `g = g'` and `h ~ h'`, or `h = h'` and `g ~ g'` — Mathlib's `SimpleGraph.boxProd`, `G □ H`.
* `Question2` / `question2` — does `n`-monophilic propagate from `n` to `n+1` for an `n`-colourable
  graph? In modern language this asks whether `ν(G) = τ(G)` for every graph; it is Question 2 of
  Allred–Mudrock and Question 1 of Chi et al. 2026, both of which trace it to this paper. See
  `provenance.md` §4.
* `not_ecc_two_boxProd_path_two_three` — **not open**, merely unformalized: the paper's own
  negative answer to Question 1 at `n = 2`.

## Two notes on §6 as printed

The restriction to `n ≥ 3` in `Question1` is the paper's: it observes that the answer at `n = 2` is
*No*, so the unrestricted statement is false and `Question1` would be a mis-statement without the
hypothesis.

The paper supports that observation with "by Theorem 3 every `Pᵢ` is 2-monophilic". **There is no
Theorem 3** — the paper has Theorems 1 and 2 only. The intended reference is the Kostochka–Sidorenko
corollary of §2, since paths are chordal (`SimpleGraph.ecc_of_isChordal`). A dangling
cross-reference, not a mathematical error; recorded in `formalization.yaml` under `errata`.
-/

open SimpleGraph

namespace ListColoring
namespace OpenProblem

/-- Adjacency in a Cartesian product is decidable when it is decidable in both factors and both
vertex types have decidable equality. Mathlib does not supply this instance at the pinned revision,
and `ECCAt` cannot be stated for `G □ H` without it. -/
instance instDecidableRelBoxProd {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) [DecidableRel G.Adj] (H : SimpleGraph β) [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj :=
  fun _ _ => decidable_of_iff' _ boxProd_adj

/-! ### Question 1 -/

/-- **Kirov–Naimi 2016, §6, Question 1.** *Is the product of two `n`-monophilic graphs
`n`-monophilic?*

The paper motivates it as a counting analogue of the List Colouring Conjecture: the line graph of
`K_{n,n}` is `Kₙ □ Kₙ`, so a positive answer would be to Galvin's theorem what enumerative
chromatic-choosability is to choosability.

`n ≥ 3` is the paper's own restriction — see the module docstring and
`not_ecc_two_boxProd_path_two_three`. -/
def Question1 : Prop :=
  ∀ (n : ℕ), 3 ≤ n →
    ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (G : SimpleGraph α) [DecidableRel G.Adj] (H : SimpleGraph β) [DecidableRel H.Adj],
      G.ECCAt n → H.ECCAt n → (G □ H).ECCAt n

/-- **Open.** Question 1 of Kirov–Naimi §6, in the direction the paper conjectures. Unproved and
unrefuted; the `sorry` records that, and is not a gap in the formalization of the paper. -/
theorem question1 : Question1 := sorry

/-- **Not open — known, and merely unformalized here.** Kirov–Naimi's negative answer to Question 1
at `n = 2`: the `2 × 3` grid `P₂ □ P₃` is not enumeratively chromatic-choosable at `2`, while every
path is (paths are chordal, so `SimpleGraph.ecc_of_isChordal` applies).

The paper derives this from Theorem 2 — all cycles of the grid are even, and it contains two cycles
whose union is not `K₂,₃` — so `ListColoring.ecc_two_iff` is the route to a proof. `pathG k` is the
path of length `k`, on `k + 1` vertices, so `pathG 2 □ pathG 3` is the `3 × 4` grid on 12
vertices. -/
theorem not_ecc_two_boxProd_path_two_three : ¬ (pathG 2 □ pathG 3).ECCAt 2 := sorry

/-! ### Question 2 -/

/-- **Kirov–Naimi 2016, §6, Question 2.** *If a graph is `n`-colourable and `n`-monophilic, is it
necessarily `(n+1)`-monophilic?*

The paper poses it to decide whether the two natural definitions of a "monophilic number" agree:
the least `n` for which `G` is `n`-colourable and `n`-monophilic, versus the least `n` such that `G`
is `n'`-monophilic for every `n' ≥ n`. In the modern vocabulary those are `ν(G)` and `τ(G)`, and
this asks whether `ν = τ` always.

The `Colorable n` hypothesis is not decoration: below the chromatic number every graph is
enumeratively chromatic-choosable for free (`SimpleGraph.ecc_of_not_colorable`), so without it the
statement would have to survive a vacuous hypothesis at every `n < χ(G)`. -/
def Question2 : Prop :=
  ∀ (n : ℕ) {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj],
    G.Colorable n → G.ECCAt n → G.ECCAt (n + 1)

/-- **Open.** Question 2 of Kirov–Naimi §6, in the direction the paper conjectures. Equivalently:
`ν(G) = τ(G)` for every graph. Unproved and unrefuted. -/
theorem question2 : Question2 := sorry

/-- What Kirov–Naimi's Theorem 2 settles is `ν(G) = 2`, the *pointwise* property at `n = 2`.
Allred–Mudrock's Theorem 10 obtains the same classification for `τ(G) = 2`, so the `χ = 2` case of
Question 2 is known; the general case is not. This is why `ListColoring.ecc_two_iff` is a statement
about `ECCAt _ 2` and not about `SimpleGraph.ECC`. -/
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) :
    G.ECCAt 2 ↔ CoreIsVertex G ∨ CoreIsCycle G ∨ CoreIsK23 G ∨ HasOddCycle G :=
  ecc_two_iff G hG

end OpenProblem
end ListColoring
