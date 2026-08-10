/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Monophilic.TwoCycles

/-!
# Rubin's structural argument: bridging Mathlib's cycles to the index form

**Attribution.** Everything in this file serves the hard direction of **Rubin's theorem**
(A. L. Rubin, in P. Erdős, A. L. Rubin and H. Taylor, *Choosability in graphs*, Proc. West Coast
Conf. on Combinatorics, Graph Theory and Computing (Arcata, California, 1979), Congr. Numer. **26**,
Utilitas Math., Winnipeg, **1980**, 125–157, pp. 131–134). Nothing here is novel; the content of
this file in particular is **mechanization**, not mathematics — it converts between two encodings of
"a cycle" that a paper would not distinguish.

## Why this file exists

`Monophilic.TwoCycles` states its non-choosability results over cycles presented as **index
sequences** — a function `A : ℕ → V` with `G.Adj (A i) (A (i+1))` for `i < m` and `G.Adj (A m)
(A 0)` — because that is what the colour-forcing chains are written against. Mathlib presents a
cycle as a `SimpleGraph.Walk` together with `Walk.IsCycle`. Rubin's argument produces the latter, so
something has to convert.

That conversion is this file. `Monophilic.ofCycleWalk` takes `hc : c.IsCycle` for `c : G.Walk v v`
and produces the index data, with the three facts the dumbbell and figure-eight results need:
adjacency along the cycle, closure at the end, and injectivity.

## The proof this feeds

Rubin's five types, and where each is discharged:

1. an odd cycle — `Monophilic.not_choosable_two_of_contains_odd_cycle`;
2. two node-disjoint even cycles joined by a path — `Monophilic.not_choosable_two_of_dumbbell`;
3. two even cycles sharing exactly one node — `Monophilic.not_choosable_two_of_figureEight`;
4. `θ_{a,b,c}` with `a ≠ 2` and `b ≠ 2` — `Monophilic.choosable_two_gtheta_iff`;
5. a generalized theta on four or more arms — `Monophilic.not_choosable_two_gtheta_of_four`.

All five are **proved**. What remains of the hard direction is the *structural extraction*: that a
core not in `{K₁, C_{2m+2}, θ_{2,2,2m}}` contains one of the five. See `plan.md` for the plan, taken
from Rubin's own argument, which runs on a shortest cycle and two shortest connecting paths and
needs **no** ear decomposition, Menger, or 2-connectivity.

## Main results

* `Monophilic.cycleWalk_adj` — adjacency along a cycle walk, in index form
* `Monophilic.cycleWalk_closes` — the closing edge
* `Monophilic.cycleWalk_injOn` — injectivity on `Set.Iic (c.length - 1)`
* `Monophilic.two_le_cycleWalk_bound` — a cycle has `2 ≤ c.length - 1`
* `Monophilic.not_choosable_two_of_two_cycle_walks` — types 2 and 3, from Mathlib cycles
-/

namespace Monophilic

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### The bridge

A cycle walk `c : G.Walk v v` of length `L` visits `L` distinct vertices, `c.getVert 0, …,
c.getVert (L-1)`, and closes because `c.getVert L = v = c.getVert 0`. So the index form takes
`A := c.getVert` and `m := L - 1`. Mechanization only. -/

/-- A cycle has length at least `3`, so the index bound `m = length - 1` is at least `2` — which is
the hypothesis `Monophilic.not_choosable_two_of_dumbbell` asks for. -/
theorem two_le_cycleWalk_bound {v : V} {c : G.Walk v v} (hc : c.IsCycle) : 2 ≤ c.length - 1 := by
  have := hc.three_le_length
  omega

/-- Consecutive vertices of a cycle walk are adjacent, indexed from `0`. -/
theorem cycleWalk_adj {v : V} (c : G.Walk v v) {i : ℕ} (hi : i < c.length - 1) :
    G.Adj (c.getVert i) (c.getVert (i + 1)) :=
  c.adj_getVert_succ (by omega)

/-- The closing edge of a cycle walk: the last distinct vertex is adjacent to the first. -/
theorem cycleWalk_closes {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    G.Adj (c.getVert (c.length - 1)) (c.getVert 0) := by
  have h3 := hc.three_le_length
  have hadj := c.adj_getVert_succ (i := c.length - 1) (by omega)
  have hlen : c.length - 1 + 1 = c.length := by omega
  rw [hlen, c.getVert_length] at hadj
  rw [c.getVert_zero]
  exact hadj

/-- A cycle walk visits `c.length` distinct vertices: `getVert` is injective on `Set.Iic
(c.length - 1)`. This is Mathlib's `SimpleGraph.Walk.IsCycle.getVert_injOn'`, restated with
`Set.Iic` so that it matches `Monophilic.not_choosable_two_of_dumbbell`. -/
theorem cycleWalk_injOn {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    Set.InjOn c.getVert (Set.Iic (c.length - 1)) :=
  hc.getVert_injOn'

/-! ### Rubin's types 2 and 3, from Mathlib cycles

Two even cycles meeting in at most one vertex are **not** enough on their own — two *disjoint* even
cycles are `2`-choosable, since each is and colourings of a disjoint union are independent. Rubin's
types 2 and 3 therefore come with a connecting path (type 2) or a shared vertex (type 3, the
degenerate case of the path having length `0`). `Monophilic.not_choosable_two_of_dumbbell` covers
both. -/

/-- **Rubin's types 2 and 3, stated over Mathlib's cycles.** Given two cycle walks joined by a path
which is internally disjoint from both, the graph is not `2`-choosable.

The disjointness hypotheses are exactly those of `Monophilic.not_choosable_two_of_dumbbell`,
transported along the `getVert` bridge; the length-`0` path gives Rubin's type 3. -/
theorem not_choosable_two_of_two_cycle_walks {v w : V} {c₁ : G.Walk v v} {c₂ : G.Walk w w}
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle) {l : ℕ} (P : ℕ → V)
    (hP : ∀ j, j < l → G.Adj (P j) (P (j + 1)))
    (hP₀ : P 0 = c₁.getVert 0) (hPl : P l = c₂.getVert 0)
    (hPinj : Set.InjOn P (Set.Iic l))
    (hAP : ∀ i, i ≤ c₁.length - 1 → ∀ j, 1 ≤ j → j ≤ l → c₁.getVert i ≠ P j)
    (hAB : ∀ i, i ≤ c₁.length - 1 → ∀ k, 1 ≤ k → k ≤ c₂.length - 1 →
      c₁.getVert i ≠ c₂.getVert k)
    (hPB : ∀ j, j ≤ l → ∀ k, 1 ≤ k → k ≤ c₂.length - 1 → P j ≠ c₂.getVert k) :
    ¬ G.Choosable 2 :=
  not_choosable_two_of_dumbbell (two_le_cycleWalk_bound hc₁) (two_le_cycleWalk_bound hc₂)
    c₁.getVert P c₂.getVert
    (fun _ hi => cycleWalk_adj c₁ hi) (cycleWalk_closes hc₁)
    hP (fun _ hk => cycleWalk_adj c₂ hk) (cycleWalk_closes hc₂)
    hP₀ hPl (cycleWalk_injOn hc₁) hPinj (cycleWalk_injOn hc₂) hAP hAB hPB

end Monophilic
