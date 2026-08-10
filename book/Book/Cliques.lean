import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Cones over Cliques" =>

%%%
tag := "cliques"
%%%

Source: [Iso.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Iso.lean),
[Cone.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Cone.lean),
[Chordal.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Chordal.lean).

The first substantial result in the paper is also the cheapest, and it is a good place to see the
counting machinery earn its keep. Attach a new vertex to a clique of a graph enumeratively
chromatic-choosable at `n`; the result is still enumeratively chromatic-choosable at `n`. Iterating
gives Kostochka and Sidorenko's observation {citep kostochkaSidorenko}[] that chordal graphs are
enumeratively chromatic-choosable at `n` for every `n`.

# The construction

The construction attaches one new vertex to a chosen set `K` of existing ones. When `K` is a clique
— pairwise adjacent — the new vertex together with `K` forms a larger clique, and that is the case
Lemma 1 is about:

```diagram (cssWidth := "62%")
open Illuminate Diagram in
let v (x y : Float) : Diagram _ := translate x y (circle 8)
let e (x1 y1 x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
-- the clique K, drawn as a triangle
let k := [v 0 0, v 110 0, v 55 (-90)]
let kEdges := [e 0 0 110 0, e 110 0 55 (-90), e 55 (-90) 0 0]
-- the rest of G, hanging off the clique
let rest := [v (-90) (-60), v (-70) 30]
let restEdges := [e (-90) (-60) 0 0, e (-70) 30 0 0, e (-90) (-60) 55 (-90)]
-- the new vertex, joined to every vertex of K
let newV := [v 55 100]
let newEdges := [e 55 100 0 0, e 55 100 110 0, e 55 100 55 (-90)]
let labels := [translate 55 126 (text "the new vertex"), translate 55 (-116) (text "clique K")]
(kEdges ++ restEdges ++ newEdges ++ k ++ rest ++ newV ++ labels).foldl atop emptyDiagram
```

Adding a vertex means changing the vertex type, and as with deletion we use `Option V` so that the
new vertex is `none` and the old graph sits underneath unchanged.

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) (a b : V) :
    ((coneOn G K).Adj (some a) (some b) ↔ G.Adj a b) ∧
    ((coneOn G K).Adj none (some b) ↔ b ∈ K) :=
  ⟨Iff.rfl, Iff.rfl⟩
```

# Counting the extensions

Given a coloring of `G`, how many ways are there to extend it across the new vertex? Exactly as many
as there are colors in the new vertex's list that its neighbors have not already used. Summing over
colorings of `G` gives the count for the cone, and — this is worth noting — the statement needs no
hypothesis on `K` whatsoever:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V} (M : ListAssignment (Option V)) :
    (coneOn G K).col M = ∑ f ∈ G.colorings (M ∘ some), ((M none) \ (K.image f)).card :=
  col_coneOn M
```

The clique hypothesis enters only when we want the sum to collapse. If `K` is a clique then every
proper coloring is injective on it, so the image `K.image f` always has exactly `K.card` elements,
and with a uniform palette the number of leftover colors is the same for every `f`:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V}
    (hK : G.IsClique (K : Set V)) (n : ℕ) :
    (coneOn G K).colConst n = (n - K.card) * G.colConst n :=
  colConst_coneOn hK n
```

The subtraction here is truncated, and it is worth pausing on why that is harmless rather than
merely convenient. If `K.card > n` there is no proper coloring of `K` from an `n`-color palette at
all, so `G.colConst n` is zero and both sides vanish; the `n - K.card = 0` on the right is not
papering over anything. If `K.card = n`, colorings of `G` exist but exhaust the palette on `K`,
leaving nothing for the new vertex — again both sides are zero. Only when `K.card < n` does the
identity have content, and there it is exact.

# Lemma 1

For an arbitrary `n`-assignment the same argument gives an inequality rather than an equality —
`K.image f` might be smaller than `K` — and that is precisely the direction needed:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V}
    (hK : G.IsClique (K : Set V)) {n : ℕ} (hG : G.ECCAt n) :
    (coneOn G K).ECCAt n :=
  SimpleGraph.ECCAt.coneOn hK hG
```

That is Lemma 1. The proof is three lines of arithmetic on top of the two counting results: the
cone's uniform count is `(n - |K|)` times `G`'s, the cone's arbitrary count is at least `(n - |K|)`
times `G`'s, and `G` is enumeratively chromatic-choosable.

# Complete graphs

Iterating Lemma 1 along a simplicial elimination ordering gives Kostochka and Sidorenko's corollary.
The cleanest instance is the complete graph, obtained by coning repeatedly over the whole vertex
set:

```lean
open SimpleGraph in
example (m n : ℕ) : (⊤ : SimpleGraph (Fin m)).ECCAt n :=
  ecc_top_fin m n
```

# The general statement

Complete graphs are only the easiest instance. What Kostochka and Sidorenko actually observed is
that *every chordal graph* is enumeratively chromatic-choosable at `n`, and the route is an
induction along a simplicial elimination ordering — which is to say, along a tower of cones over
cliques. That is directly expressible:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ} (hG : G.ECCAt n) :
    ∀ (k : ℕ) (d : CliqueTowerData V k), CliqueTowerData.IsSimplicial G k d →
      (cliqueTower G k d).ECCAt n :=
  ecc_cliqueTower hG
```

Starting the tower from the empty graph gives the corollary in the form the paper uses: anything
built along a simplicial elimination ordering is enumeratively chromatic-choosable at `n`, for every
`n`. Each step is one application of Lemma 1; the induction adds nothing beyond bookkeeping.

Two remarks on what this does and does not settle. Dirac's theorem {citep dirac}[] is what connects
"has a simplicial elimination ordering" to the usual definition of chordal — every cycle longer than
a triangle has a chord. That equivalence is a convenience for *recognizing* chordal graphs; it is
not a step in the argument, and this development does not have it. So what is proved here is exactly
the ordering form, and no more.

The second remark is a pleasant consistency check. The pendant towers used for Lemma 5 in a later
chapter are a special case of these clique towers, since a singleton is a clique — and the two
constructions are provably the same graph, so Lemma 5's easy direction can be rederived from the
theorem above rather than proved separately.

It is also worth noticing what the formalization *removed* from the expected dependency list. A
first reading of the literature suggests that counting colorings requires the chromatic polynomial,
and hence deletion–contraction and Whitney's broken-cycle theorem. It does not. Nothing in
Kirov–Naimi needs the count to be exhibited as a polynomial in `n`; it needs the count. Dropping the
polynomial layer removes edge contraction from the critical path entirely.
