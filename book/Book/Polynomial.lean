import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "The Chromatic Polynomial" =>

%%%
tag := "polynomial"
%%%

Source:
[ChromaticPolynomial.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/ChromaticPolynomial.lean),
[ListColorFunction.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/ListColorFunction.lean).

Look again at the counts from the previous chapter, read as functions of the number of colours `n`:

* edgeless graph on `v` vertices: $`n^{v}`;
* tree on `v` vertices: $`n(n-1)^{v-1}`;
* complete graph $`K_m`: $`n(n-1)\cdots(n-m+1)`;
* cycle on `v` vertices: $`(n-1)^{v} + (-1)^{v}(n-1)`.

Every one is a polynomial in `n` with integer coefficients, of degree $`|V|`, monic, with
alternating signs. That is not a coincidence about these four families. It is a theorem about all
graphs, discovered by Birkhoff in 1912 while trying to prove the four-colour theorem by counting
colourings rather than exhibiting one.

*For every finite graph `G` there is a polynomial $`P(G, X) \in \mathbb{Z}[X]` such that
$`P(G, n) = \mathrm{col}(G, n)` for every natural number `n`.*

This chapter builds that polynomial and says why it is built the way it is.

# Why not deletion–contraction

The textbook proof is a two-line induction. Pick an edge `uv`. A colouring of `G - uv` either gives
`u` and `v` different colours — and is then a colouring of `G` — or gives them the same colour, and
is then a colouring of the graph `G / uv` in which `u` and `v` have been *merged into one vertex*.
So

$$`P(G, X) = P(G - uv, X) - P(G/uv, X)`

and induction on the number of edges does the rest, the base case being the edgeless graph.

It is a beautiful argument and it is unavailable here. Contraction merges two vertices, which means
the vertex *type* changes to a quotient; and Mathlib, at the revision this development builds
against, has no edge contraction for `SimpleGraph` at all. Building one is not a formality:
contracting an edge of a simple graph can create parallel edges, so the honest construction lands in
multigraphs, and the induction then has to be redone in a setting the rest of the development does
not use.

There is a second, quieter reason to avoid it. The recursion computes the polynomial but tells you
nothing about the *lists*. The whole point of the later chapters is to compare
$`\mathrm{col}(G, n)` against counts from non-uniform lists, and deletion–contraction has no
list-coloured analogue — contracting `uv` when `u` and `v` have different lists is meaningless.

# Whitney's subset expansion

So we take a different formula as the definition. For a set `S` of edges, write `c(S)` for the
number of connected components of the graph on all of `V` whose edges are exactly those in `S`.
Then

$$`P(G, X) = \sum_{S \subseteq E(G)} (-1)^{|S|}\, X^{\,c(S)}.`

That this is a polynomial is immediate — it is a signed sum of powers of `X`. That it counts
colourings is one inclusion–exclusion computation, not an induction.

Here is the whole of it. Fix a palette of `n` colours. For a subset `S` of edges, the number of
functions $`V \to \{0,\dots,n-1\}` that are *constant along every edge of `S`* is exactly
$`n^{c(S)}`: such a function is constant on each component of `(V, S)`, and the components may be
coloured independently. Now expand the product $`\prod_{e \in E}(1 - [\,e \text{ monochromatic}\,])`
— which is `1` for a proper colouring and `0` otherwise — over subsets of `E`, and sum over all
functions. The two sums are the two sides of the formula.

Turning to the triangle, whose three edges give eight subsets:

```diagram (cssWidth := "92%")
open Illuminate Diagram in
let v (x y : Float) : Diagram SVG := translate x y (circle 7)
let e (x1 y1 x2 y2 : Float) : Diagram SVG := line ⟨x1, y1⟩ ⟨x2, y2⟩
-- four panels: the same three vertices, with the edges of S drawn in
let verts := [v 0 40, v (-38) (-30), v 38 (-30),
              v 190 40, v 152 (-30), v 228 (-30),
              v 380 40, v 342 (-30), v 418 (-30),
              v 570 40, v 532 (-30), v 608 (-30)]
let edges := [e 190 40 152 (-30),
              e 380 40 342 (-30), e 380 40 418 (-30),
              e 570 40 532 (-30), e 570 40 608 (-30), e 532 (-30) 608 (-30)]
let labels := [translate 0 (-70) (text "|S| = 0, c = 3"),
               translate 190 (-70) (text "|S| = 1, c = 2"),
               translate 380 (-70) (text "|S| = 2, c = 1"),
               translate 570 (-70) (text "|S| = 3, c = 1")]
(edges ++ verts ++ labels).foldl atop emptyDiagram
```

:::table +header (align := left)
*
  * shape of `S`
  * how many
  * $`|S|`
  * $`c(S)`
  * contribution
*
  * no edges
  * `1`
  * `0`
  * `3`
  * $`+X^3`
*
  * one edge
  * `3`
  * `1`
  * `2`
  * $`-3X^2`
*
  * two edges
  * `3`
  * `2`
  * `1`
  * $`+3X`
*
  * all three
  * `1`
  * `3`
  * `1`
  * $`-X`
:::

Adding up: $`X^3 - 3X^2 + 2X = X(X-1)(X-2)`, which is what colouring three mutually adjacent
vertices one at a time gives. Note how the two `c(S) = 1` rows partly cancel — the expansion is not
term-by-term meaningful, only in total.

In Lean the definition is the displayed sum, verbatim:

```lean
open Finset SimpleGraph Polynomial in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.chromaticPolynomial = ∑ S ∈ G.edgeFinset.powerset, (-1) ^ S.card * X ^ compCount S :=
  rfl
```

with `compCount S` the number of components:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V] (S : Finset (Sym2 V)) :
    compCount S = Fintype.card (fromEdgeSet (S : Set (Sym2 V))).ConnectedComponent :=
  rfl
```

and the theorem that makes it the right object is the evaluation lemma:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    (G.chromaticPolynomial).eval (n : ℤ) = (G.colConst n : ℤ) :=
  eval_chromaticPolynomial G n
```

This single lemma is the whole bridge. Everywhere else in this book we count; here, and only here,
is the count identified with a polynomial.

# A computable twin

`Polynomial` and `Polynomial.eval` are noncomputable in Mathlib, so the definition above cannot be
run. The same sum with an integer in place of `X` can be:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : ℤ) :
    G.whitneySum x = ∑ S ∈ G.edgeFinset.powerset, (-1) ^ S.card * x ^ compCount S :=
  rfl
```

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : ℤ) :
    (G.chromaticPolynomial).eval x = G.whitneySum x :=
  eval_chromaticPolynomial_eq_whitneySum G x
```

That is enough to make the triangle's polynomial checkable by the kernel rather than by the reader.
$`X(X-1)(X-2)` at `3` is `6` and at `4` is `24`:

```lean
open SimpleGraph in
example : (⊤ : SimpleGraph (Fin 3)).whitneySum 3 = 6 := by decide
```

```lean
open SimpleGraph in
example : (⊤ : SimpleGraph (Fin 3)).whitneySum 4 = 24 := by decide
```

Cross-checks like these are worth more than they look. The subset expansion is easy to state
slightly wrong — an off-by-one in `c(S)`, a sign convention — and a wrong version would still be *a*
polynomial and would still admit a plausible-looking correctness proof sketch. Running it against
directly computed colouring counts is what rules that out.

# Worked values

*The edgeless graph.* One subset, one term:

```lean
open SimpleGraph Polynomial in
example {V : Type} [Fintype V] [DecidableEq V] [DecidableRel (⊥ : SimpleGraph V).Adj] :
    chromaticPolynomial (⊥ : SimpleGraph V) = X ^ Fintype.card V :=
  chromaticPolynomial_bot
```

so its degree is the number of vertices — which is the degree of every chromatic polynomial, and the
only case where that is visible without work:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V] [DecidableRel (⊥ : SimpleGraph V).Adj] :
    (chromaticPolynomial (⊥ : SimpleGraph V)).natDegree = Fintype.card V :=
  natDegree_chromaticPolynomial_bot
```

```lean
open SimpleGraph in
example : (⊥ : SimpleGraph (Fin 3)).whitneySum 3 = 27 := by decide
```

*The path on three vertices.* Two edges, four subsets: $`X^3 - 2X^2 + X = X(X-1)^2`, which is `12`
at `X = 3` — the number computed directly in the previous chapter.

```lean
open ListColoring SimpleGraph in
example : ((pathG 2).chromaticPolynomial).eval ((3 : ℕ) : ℤ) = 12 := by
  rw [eval_chromaticPolynomial, show (pathG 2).colConst 3 = 12 from by decide]
  norm_num
```

*The cycle.* This is the one family whose polynomial is not obvious, and it is the family Theorem 1
is about. For the cycle on `v = k + 2` vertices and `n = m + 2` colours:

```lean
open ListColoring in
example (m k : ℕ) :
    (((closePath (k + 1)).colConst (m + 2) : ℤ))
      = ((m + 1) : ℤ) ^ (k + 2) + (-1) ^ (k + 2) * ((m + 1) : ℤ) :=
  colConst_closePath_chromatic m k
```

Read with $`n = m + 2` and $`v = k + 2` this says $`\mathrm{col}(C_v, n) = (n-1)^v + (-1)^v (n-1)`.
The offsets `m + 2` and `k + 1` are not decoration: they are how "at least two colours" and "at
least three vertices" are expressed to Lean without a side condition, so that the statement holds
for every `m` and `k` with no hypotheses at all.

Sanity: at `n = 2` and `v` even the formula gives $`1 + 1 = 2`, the two alternating colourings; at
`n = 2` and `v` odd it gives $`1 - 1 = 0`. At `v = 3`, $`(n-1)^3 - (n-1) = n(n-1)(n-2)`, the
triangle again.

# What the polynomial buys

Two things, and it is worth being precise about which.

It buys *vocabulary*. The literature on this subject is written in terms of the chromatic polynomial
$`P(G, n)` and its list analogue $`P_\ell(G, n)`, introduced in the next chapter, and the central
question is stated as an equality between them. Without the polynomial one can still state the
question — it is the definition of enumerative chromatic-choosability — but not in the words
everyone else uses.

It does *not* buy any of the proofs. Nothing in the argument for cycles, for chordal graphs, or for
the classification at `n = 2` uses polynomiality. Those arguments count, and counting is enough. The
one place the expansion earns its keep as a tool rather than as vocabulary is
{ref "threshold"}[the threshold theorem], where the same inclusion–exclusion is run with arbitrary
lists in place of a uniform palette.
