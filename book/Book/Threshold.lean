import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Every Graph, Eventually" =>

%%%
tag := "threshold"
%%%

Source:
[Threshold.lean](https://github.com/rkirov/enumerative-chromatic-choosability/blob/main/ListColoring/Threshold.lean),
[ChromaticPolynomial.lean](https://github.com/rkirov/enumerative-chromatic-choosability/blob/main/ListColoring/ChromaticPolynomial.lean).

Cycles are enumeratively chromatic-choosable for every `n`. Chordal graphs are enumeratively
chromatic-choosable for every `n`. $`\theta_{2,2,4}` is not enumeratively chromatic-choosable at
`2`. Is it `3`-enumeratively chromatic-choosable? `10`-enumeratively chromatic-choosable?

Donner {citep donner}[] answered the general form of that question in 1992: *every* graph is
enumeratively chromatic-choosable at `n` once `n` is large enough. This chapter states his theorem,
gives an explicit threshold, and says why the threshold here is far worse than the best one known.

# Donner's theorem

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ N, ∀ k, N ≤ k → G.ECCAt k :=
  exists_ecc_forall_ge G
```

Equivalently, in the notation of the literature: for every graph the list colour function eventually
agrees with the chromatic polynomial.

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ N, ∀ k, N ≤ k → G.listColorFunction k = G.colConst k :=
  exists_listColorFunction_eq_forall_ge G
```

So the failures of enumerative chromatic-choosability are always a low-`n` phenomenon. That reframes
everything in this book: the classification at `n = 2` is a description of the *hardest* case, and
the theorem about cycles says that for cycles the hard case never occurs at all.

Donner's own proof is non-constructive and yields no bound. What is proved here is a bound, from
which the theorem follows immediately.

# An explicit threshold

Write `m` for the number of edges of `G`.

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 2 ^ #G.edgeFinset < k) :
    G.ECCAt k :=
  ecc_of_two_pow_lt hk
```

*More than $`2^m` colours suffice.* Donner's theorem is then one line: take $`N = 2^m + 1`.

The same statement in list-colour-function form, and against the genuine polynomial:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 2 ^ #G.edgeFinset < k) :
    G.listColorFunction k = G.colConst k :=
  listColorFunction_eq_of_two_pow_lt hk
```

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 2 ^ #G.edgeFinset < k) :
    (G.listColorFunction k : ℤ) = (G.chromaticPolynomial).eval (k : ℤ) :=
  listColorFunction_eq_eval_of_two_pow_lt hk
```

The bound is crude. $`\theta_{2,2,4}` has eight edges,

```lean
open ListColoring in
example : (theta 2).edgeFinset.card = 8 := by decide
```

so the theorem above guarantees enumerative chromatic-choosability at `k` only from `k = 257`
onwards, while the graph is in fact already not enumeratively chromatic-choosable at `2`, and
nothing worse. No claim is made that the threshold is anywhere near sharp; the claim is that it is
explicit and self-contained.

# How it is proved

The engine is the Whitney expansion of {ref "polynomial"}[the chromatic polynomial chapter], run
with *arbitrary* lists rather than a uniform palette. This is the one place in the development where
the subset expansion is a tool rather than a piece of vocabulary.

For a set `S` of edges, let $`N_L(S)` be the number of colourings from `L` that are constant along
every edge of `S`. Such a colouring is constant on each connected component of $`(V, S)`, and on a
component `C` it may use any colour lying in *every* list of `C`; the components are independent, so

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (L : ListAssignment V) (S : Finset (Sym2 V)) :
    listCount L S = ∏ C : (edgeGraph S).ConnectedComponent, #(compInter L S C) :=
  listCount_eq_prod L S
```

Inclusion–exclusion over the edge set then expands the list colouring count:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (L : ListAssignment V) :
    (G.col L : ℤ)
      = ∑ S ∈ G.edgeFinset.powerset, (-1) ^ #S * (listCount L S : ℤ) :=
  col_eq_sum_powerset G L
```

For a uniform palette every intersection is the whole palette, so the product collapses to
$`k^{c(S)}` and the expansion is exactly the chromatic polynomial again:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V] (k : ℕ) (S : Finset (Sym2 V)) :
    listCount (constList V k) S = k ^ compCount S :=
  listCount_constList k S
```

Subtracting the two expansions turns the goal — that the uniform count is smallest — into a
statement about the *defects* $`d(S) = k^{c(S)} - N_L(S)`, each of which is nonnegative because an
intersection of lists is no larger than a single list. The difference is an alternating sum of
defects, and the argument is a matter of showing that the `+` terms dominate.

Four estimates do it.

*A product of `c` factors, each at most `k`, falls short of $`k^c` by at most $`k^{c-1}` times the
total shortfall of the factors.* This turns a defect on a component into a sum of per-vertex
deficiencies.

*The deficiency of a set of vertices grows by at most $`k - |L(u) \cap L(w)|` when a new vertex `w`
adjacent to some `u` already in the set is adjoined.* Growing each component one boundary edge at a
time therefore bounds the total defect of `(V, S)` by
$`t = \sum_{e \in S}\bigl(k - |L(u) \cap L(v)|\bigr)`, a quantity depending only on `L` and not on
`S`.

*Two distinct edges of a simple graph span at least three vertices and merge two independent pairs*,
so $`c(S) \le |V| - 2` as soon as $`|S| \ge 2`.

*The singleton terms are exact*: the terms with $`|S| = 1` contribute precisely
$`k^{|V|-2} \cdot t`.

Put together: the term $`S = \emptyset` contributes nothing, the singletons contribute
$`k^{|V|-2} t` with a favourable sign, and each of the fewer than $`2^m` remaining terms is at most
$`k^{|V|-3} t` in absolute value. So the difference is at least
$`t \cdot k^{|V|-3} \cdot (k - 2^m) \ge 0`, which is the theorem.

Two things are worth noticing about this argument. It needs no connectivity hypothesis, because
$`t \ge 0` unconditionally — in the sharp forms of the theorem connectivity is assumed and does
work. And it never mentions choosability, enumerative chromatic-choosability at smaller `n`, or any
of the structure the rest of the book is about; it is pure counting with a crude bound at the end.

# The sharper threshold, and why we stop short

Thomassen {citep thomassen}[] gave the first explicit bound, and Wang, Qian and Yan
{citep wangQianYan}[] brought it down to

$$`k > \frac{m-1}{\ln(1 + \sqrt{2})} \approx 1.135\,(m-1),`

which is linear in the number of edges rather than exponential. The comparison for the graphs of
this book:

:::table +header (align := left)
*
  * graph
  * edges `m`
  * least `k` here, $`2^m + 1`
  * least `k` sharp, $`\lceil 1.135(m-1)\rceil`
*
  * four-cycle
  * `4`
  * `17`
  * `4`
*
  * $`K_{2,3} = \theta_{2,2,2}`
  * `6`
  * `65`
  * `6`
*
  * $`\theta_{2,2,4}`
  * `8`
  * `257`
  * `8`
:::

```lean
open ListColoring in
example : (theta 1).edgeFinset.card = 6 := by decide
```

The gap is not a small inefficiency; it is the difference between a bound one could use and a bound
one can only state.

The reason we do not reach the sharp bound is specific and worth recording. The Wang–Qian–Yan
argument runs over the *broken cycle* form of Whitney's theorem — the expansion of the chromatic
polynomial over the subsets of edges containing no broken cycle, which cancels the alternating sum
down to a sum with far fewer terms. Mathlib has no broken cycle theorem, and proving one is a
project in its own right: it needs a linear order on the edges, the notion of a broken cycle, and a
sign-reversing involution on the subsets that are not broken-cycle-free. Everything in this chapter,
by contrast, is a few hundred lines resting only on `SimpleGraph.fromEdgeSet` and
`SimpleGraph.ConnectedComponent`.

That trade — a much worse constant for a self-contained proof — is the same one made in
{ref "polynomial"}[the chromatic polynomial chapter], where the subset expansion was preferred to
deletion–contraction for the same kind of reason. It is a recurring shape in formalization: the
argument that is shortest on paper is often the one that needs the most infrastructure, and the
argument that needs none may cost only a constant.

# Where this leaves the subject

Between them the results of this book bracket the question. Below the list chromatic number
enumerative chromatic-choosability is either vacuous or impossible. Above $`2^m` it is automatic. In
between lies everything interesting, and what is known there is: chordal graphs always, cycles
always, and at `n = 2` a complete classification. For `n ≥ 3` on a general graph, the honest answer
is that nobody knows.

Two directions in the modern literature are worth naming. Kaul and Mudrock {citep kaulMudrock}[]
study the same equality for DP-colourings, a strengthening of list colouring in which even the
identification of colours across an edge is allowed to vary; the analogous "DP colour function" can
fail to equal the chromatic polynomial for arbitrarily large `n`, so the eventual-agreement theorem
of this chapter genuinely uses something about lists.

And choosability itself remains a subject without a classification. On the positive side Galvin
{citep galvin}[] proved that for the *edge* colourings of a bipartite multigraph the list chromatic
index equals the chromatic index — one of the few places where lists cost nothing at all. On the
negative side, deciding `2`-choosability is easy by Rubin's theorem, while deciding
`3`-choosability is NP-hard even for planar graphs {citep gutner}[]. The `n = 2` classification of
{ref "twoecc"}[the previous chapter] sits right at that boundary, which is part of why it is
the case that could be settled.
