import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Minimizing Assignments, and Cycles" =>

%%%
tag := "cycles"
%%%

Source:
[PathSplit.lean](https://github.com/rkirov/enumerative-chromatic-choosability/blob/main/ListColoring/PathSplit.lean),
[PathMinimizing.lean](https://github.com/rkirov/enumerative-chromatic-choosability/blob/main/ListColoring/PathMinimizing.lean),
[Cycle.lean](https://github.com/rkirov/enumerative-chromatic-choosability/blob/main/ListColoring/Cycle.lean),
[CycleECC.lean](https://github.com/rkirov/enumerative-chromatic-choosability/blob/main/ListColoring/CycleECC.lean),
[CycleTwo.lean](https://github.com/rkirov/enumerative-chromatic-choosability/blob/main/ListColoring/CycleTwo.lean),
[CycleRotate.lean](https://github.com/rkirov/enumerative-chromatic-choosability/blob/main/ListColoring/CycleRotate.lean).

Everything now assembles. This chapter covers the second half of Lemma 3 — which assignments
actually achieve the minimum — and then Theorem 1.

# Minimizing assignments

An assignment is *minimizing* for a graph when no other assignment with the same list sizes gives a
smaller count. Minimizers exist, and the proof is shorter than one expects. The set of candidate
assignments is infinite, because colors range over all of `ℕ`; but the set of *achievable counts* is
a nonempty set of naturals, so it has a least element:

```lean
open SimpleGraph ListColoring in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L₀ : ListAssignment V) :
    ∃ L, (∀ v, (L v).card = (L₀ v).card) ∧ G.Minimizing L :=
  exists_minimizing G L₀
```

No relabelling into a finite palette is needed. This is worth recording because the obvious route —
observe that `col` is renaming-invariant, push every assignment into `range N`, then minimize over a
finite set — is a substantial detour that buys nothing.

# Minimizers are nested, hence rigid

Now Lemma 2 does its work. Suppose a minimizing assignment on a path had two adjacent vertices with
non-nested lists. Cut the path at that edge — this is where the path must be exhibited as a bridge
of two shorter paths — and apply the swap. Both strictness hypotheses hold because each side is a
path all of whose lists have at least two colors, and a path with such lists is colorable with any
one vertex's color prescribed. The count strictly drops, contradicting minimality.

So a minimizing assignment is nested at every edge. Since interior lists all have `n` elements and
nested sets of equal size are equal, all interior lists coincide; and each terminal list, having
`n-1` elements and being nested with its `n`-element neighbor, is contained in it. That is exactly
the type A / type B shape, and its count is therefore `A_k` or `B_k`.

The immediate consequence is part (b) of Lemma 3 — a lower bound for *every* `(n,n-1)`-assignment,
minimizing or not:

```lean
open SimpleGraph ListColoring in
example {k m : ℕ} {L : ListAssignment (PathV k)} (hL : IsNNAssign k m L) :
    min (pathA m k) (pathB m k) ≤ (pathG k).col L :=
  min_pathA_pathB_le_col hL
```

Note there is no hypothesis on `n` here. At `n = 2` the bound is true but vacuous, because
`min (A_k, B_k) = 0`; the restriction to `n ≥ 3` belongs to part (c) alone.

# Where part (c) needs its hypothesis

Part (c) says a minimizing assignment is type A when `k` is odd and type B when `k` is even —
which, given `A_k - B_k = (-1)^k`, is just the statement that the minimizer realizes the smaller of
the two.

```lean
open SimpleGraph ListColoring in
example {k m : ℕ} {L : ListAssignment (PathV k)}
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hL : IsNNAssign k m L) (hmin : (pathG k).Minimizing L) :
    ∃ S x y, IsPathShape k m L S x y ∧ ((Odd k ∧ x = y) ∨ (Even k ∧ x ≠ y)) :=
  isPathShape_parity_of_minimizing hm hk hL hmin
```

The hypothesis `1 ≤ k` is not decoration. The paper's definition of an `(n,n-1)`-list assignment is
given for a path "of length at least one", and part (c) is exactly what needs that restriction. At
length zero the two terminal vertices are the same vertex; every `(n,n-1)`-assignment gives it
`n-1` colors and so every one of them is minimizing; and every shape at length zero forces the two
missing colors to coincide, i.e. type A — while `0` is even, so part (c) would demand type B. There
is a machine-checked witness of the failure in the development. At `n = 3` the two counts are
`A_0 = 2` and `B_0 = 1`, so the two types do not even have the same list sizes at length zero.

Mechanization does not find an error in the paper here. It confirms that a hypothesis stated in
passing is load-bearing, and identifies precisely which claim would fail without it.

# Cycles

A cycle is a path with its two ends joined. In this development that is *literally* the definition,
and the two graphs live on the same vertex type — which is what makes the arguments below cheap:

```diagram (cssWidth := "78%")
open Illuminate Diagram in
let v (x : Float) : Diagram SVG := translate x 0 (circle 8)
let e (x1 x2 : Float) : Diagram SVG := line ⟨x1, 0⟩ ⟨x2, 0⟩
let xs : List Float := [0, 60, 120, 180, 240, 300]
let verts := xs.map v
let edges := [e 0 60, e 60 120, e 120 180, e 180 240, e 240 300]
-- the closing edge, routed below so it does not overlap the path
let closing := [line ⟨0, -8⟩ ⟨0, -50⟩, line ⟨0, -50⟩ ⟨300, -50⟩, line ⟨300, -50⟩ ⟨300, -8⟩]
let labels := [translate 0 26 (text "pathEnd"), translate 300 26 (text "pathStart"),
               translate 150 (-66) (text "the closing edge")]
(edges ++ closing ++ verts ++ labels).foldl atop emptyDiagram
```

So `closePath k` is `pathG k` plus the single edge joining `pathStart k` to `pathEnd k`:

```lean
open SimpleGraph ListColoring in
example (k : ℕ) : closePath (k + 1) = (pathG k).addPendantPair (pathEnd k) (pathStart k) := rfl
```

Delete one vertex of a cycle and fix its color. The two neighbors both lose that one color, the rest
keep the full palette — a type A assignment on the shorter path. So each of the `n` choices
contributes `A_{k-1}`, giving the paper's `col(C, n) = n · A_{k-2}`:

```lean
open SimpleGraph ListColoring in
example (m k : ℕ) : (closePath (k + 1)).colConst (m + 2) = (m + 2) * pathA m k :=
  colConst_closePath_succ m k
```

For the other direction we must show every `n`-assignment gives at least this. When the cycle has an
odd number of vertices the path left after deletion has odd length, so `min(A, B) = A`, and part (b)
alone finishes it — with no non-constancy hypothesis and no restriction on `n`.

The even case is where the difficulty concentrates, and it is tighter than it first appears. The
tempting argument — one fibre contributes at least `A + 1`, the others at least `B` — gives only
`nA - n + 2`, which is *less* than `nA`. The paper's actual argument is stronger: once one fibre
falls below `A`, that fibre is forced to be exactly a type B shape whose palette omits some color
`c₀`, and `c₀` then certifies that every *other* fibre fails to be type B, hence is at least `A`.
The total is `B + (A+1) + (n-2)A = nA` exactly. There is no slack in it.

Putting the parities together:

```lean
open SimpleGraph ListColoring in
example {m k : ℕ} (hk : 2 ≤ k) (hm : 1 ≤ m) : (closePath k).ECCAt (m + 2) :=
  ecc_closePath hk hm
```

Every cycle, every `n ≥ 3`.

One structural remark. The paper deletes an edge `vw` chosen so that `L(v) ≠ L(w)`, which in a
formalization would seem to require a rotation automorphism of the cycle to bring that edge into
position. It turns out not to. In the deficient case the type B shape already forces the two
neighbors of the distinguished vertex to carry different lists, which is all the argument uses. The
rotation is avoidable, and the resulting proof is a little shorter than the printed one.

# The case `n = 2`

Everything above assumed `n ≥ 3`. The remaining case is the one part of Section 3 that does not
touch the `A_k` / `B_k` machinery at all: it runs on the paper's *forcing* relation, where a color
at one vertex forces a color at another when it admits exactly one extension there.

Cycles with an odd number of vertices are covered already and vacuously, since such a cycle is not
`2`-colorable. For an even number of vertices, `col(C,2) = 2`, and the argument runs on the
observation that a cycle colouring is exactly a path colouring whose two ends differ. Propagating
the forcing relation along the path shows that if *every* colour of the list at one end forces a
colour at the other, then all lists agree — so a non-constant assignment always leaves some colour
that forces nothing, and two distinct cycle colourings can be extracted from it.

That argument, as the paper presents it, deletes an edge `vw` chosen so that `L(v) ≠ L(w)`. Here the
deletable edge is fixed, so what is needed is the ability to *move* the cycle: a rotation
automorphism.

```lean
open SimpleGraph ListColoring in
example {k : ℕ} (hk : 1 ≤ k) (r : Fin (k + 1)) : closePath k ≃g closePath k :=
  rotIso hk r
```

It is built by numbering the cycle with `Fin (k+1)`, characterizing adjacency as `i + 1 = j` or
`j + 1 = i` in that group, and rotating by addition. With it, a non-constant assignment can always
be turned so that the two differing lists sit at the ends of the removed edge — and this is the only
place in the whole of Section 3 where the paper's freedom to *choose* the edge is genuinely
load-bearing rather than a convenience.

Two small strengthenings emerged. The conditional step needed no parity hypothesis at all — only
non-constancy — so `Odd k` is used solely for the constant case. And the differing pair can always
be found inside the path rather than across the wrap-around edge, since otherwise the assignment
would already be constant.

# Theorem 1, in full

```lean
open SimpleGraph ListColoring in
example {k m : ℕ} (hk : 2 ≤ k) : (closePath k).ECCAt (m + 2) :=
  ecc_closePath_of_two_le hk
```

and, transported along `ListColoring.cycleGraphIsoClosePath`, on Mathlib's cycle graph — the form
`Challenge.lean` claims:

```lean
open SimpleGraph in
example {n m : ℕ} (hn : 3 ≤ n) : (cycleGraph n).ECCAt (m + 2) :=
  ecc_cycleGraph_of_three_le hn
```

Every cycle, every `n ≥ 2`.
