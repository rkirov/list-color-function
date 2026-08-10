import VersoManual
import Book.Papers
import ListColoring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "First Answers: Chordal Graphs" =>

%%%
tag := "chordal"
%%%

Source: [Cone.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Cone.lean),
[Chordal.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Chordal.lean),
[Dirac.lean](https://github.com/rkirov/list-color-function/blob/main/ListColoring/Dirac.lean).

Which graphs are enumeratively chromatic-choosable at `n`? The first answer, and the one that came
with the question, is due to Kostochka and Sidorenko {citep kostochkaSidorenko}[]: *every chordal
graph is enumeratively chromatic-choosable at `n`, for every `n`*. This chapter explains what
chordal means, why the proof is short, and what had to be supplied to make it complete.

# One vertex at a time

The whole argument is a single step, iterated. Suppose `G` is enumeratively chromatic-choosable at
`n`, and build a new graph by adding one vertex joined to a set `K` of old ones. How does the count
change?

Given a colouring of `G`, the new vertex may take any colour of its own list that its neighbours
have not used. So the number of colourings of the new graph is

$$`\sum_{f} \bigl| L(\text{new}) \setminus f(K) \bigr|,`

the sum running over colourings `f` of `G`. Now suppose `K` is a *clique* — its vertices pairwise
adjacent. Then every proper colouring is injective on `K`, so $`|f(K)| = |K|` for every `f`, and
with a uniform palette every term of the sum is the same:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V}
    (hK : G.IsClique (K : Set V)) (n : ℕ) :
    (coneOn G K).colConst n = (n - K.card) * G.colConst n :=
  colConst_coneOn hK n
```

With arbitrary lists the image `f(K)` can only be *smaller*, so each term is at least
$`n - |K|` and the same computation gives an inequality in the direction we want. Combining the two
with enumerative chromatic-choosability of `G` gives Kirov and Naimi's Lemma 1:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V}
    (hK : G.IsClique (K : Set V)) {n : ℕ} (hG : G.ECCAt n) :
    (coneOn G K).ECCAt n :=
  SimpleGraph.ECCAt.coneOn hK hG
```

Three lines of arithmetic. The clique hypothesis is doing all the work: it is what makes the
per-colouring count *constant* in the uniform case, so that the sum factors.

# Simplicial vertices

Run the construction backwards. A vertex whose neighbours are pairwise adjacent is called
*simplicial*; deleting one is precisely undoing a cone over a clique.

```lean
open SimpleGraph in
example {V : Type} (G : SimpleGraph V) (v : V) :
    G.IsSimplicialVertex v ↔ G.IsClique (G.neighborSet v) :=
  Iff.rfl
```

```diagram (cssWidth := "80%")
open Illuminate Diagram in
let red : Fill := .solid { color := { r := 214, g := 96, b := 77 } }
let v (x y : Float) : Diagram _ := translate x y (circle 9)
let hi (x y : Float) : Diagram _ := translate x y (circle 13 red)
let e (x1 y1 x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
let edges :=
  [e (-170) 0 (-60) 95, e (-170) 0 (-60) (-95), e (-60) 95 (-60) (-95),
   e (-60) 95 60 0, e (-60) (-95) 60 0, e (-60) (-95) 110 (-110), e 60 0 110 (-110)]
let verts := [hi (-170) 0, v (-60) 95, v (-60) (-95), v 60 0, v 110 (-110)]
let labels :=
  [translate (-170) 30 (text "a"), translate (-60) 125 (text "b"),
   translate (-92) (-115) (text "c"), translate 78 26 (text "d"),
   translate 140 (-135) (text "e"),
   translate (-170) (-42) (text "simplicial")]
(edges ++ verts ++ labels).foldl atop emptyDiagram
```

In the picture `a` is simplicial: its neighbours are `b` and `c`, and `b` and `c` are joined. So is
`e`, whose neighbours `c` and `d` are joined. The vertex `c` is not: its neighbours are `a`, `b`,
`d`, `e`, and `a` is not joined to `d`.

Delete `a`; what is left is still a graph of the same kind, and it still has a simplicial vertex.
Keep going and the graph disappears entirely. Reading the deletions backwards gives a *simplicial
elimination ordering*: a way of building the graph from nothing, adding one vertex at a time, each
joined to a clique of what has been built so far.

That is exactly a tower of the cone construction, with a clique condition at every stage:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ} (hG : G.ECCAt n) :
    ∀ (k : ℕ) (d : CliqueTowerData V k), CliqueTowerData.IsSimplicial G k d →
      (cliqueTower G k d).ECCAt n :=
  ecc_cliqueTower hG
```

The induction adds nothing beyond bookkeeping: each step is one application of Lemma 1. Starting the
tower from the empty graph, which is enumeratively chromatic-choosable at `n` for the emptiest of
reasons, gives the theorem in ordering form — *anything with a simplicial elimination ordering is
enumeratively chromatic-choosable at `n`, for every `n`*.

# Chordal graphs

The usual definition of chordal is not about orderings at all. A graph is chordal when every cycle
of length at least four has a *chord*: an edge of the graph joining two vertices of the cycle that
is not itself an edge of the cycle. Equivalently, it has no induced cycle longer than a triangle.

```lean
open SimpleGraph in
example {V : Type} (G : SimpleGraph V) :
    G.IsChordal ↔
      ∀ {u : V} (c : G.Walk u u), c.IsCycle → 4 ≤ c.length → ¬ c.IsChordless :=
  Iff.rfl
```

Complete graphs are chordal, since every cycle in one has every possible chord:

```lean
open SimpleGraph in
example {V : Type} : (⊤ : SimpleGraph V).IsChordal :=
  isChordal_top
```

Cycles themselves are not, once they are long enough to have a chord to lack:

```lean
open SimpleGraph in
example : ¬ (cycleGraph 4).IsChordal := not_isChordal_cycleGraph_four
```

```lean
open SimpleGraph in
example : ¬ (cycleGraph 5).IsChordal := not_isChordal_cycleGraph_five
```

Chordality is well behaved under the two operations we care about. It survives deleting a vertex,

```lean
open SimpleGraph in
example {V : Type} {G : SimpleGraph V} (h : G.IsChordal) (v : V) :
    (G.deleteVertex v).IsChordal :=
  h.deleteVertex v
```

and it survives coning over a clique — the structural counterpart of Lemma 1:

```lean
open SimpleGraph in
example {V : Type} {G : SimpleGraph V} {K : Finset V}
    (hG : G.IsChordal) (hK : G.IsClique (K : Set V)) :
    (coneOn G K).IsChordal :=
  hG.coneOn hK
```

# Dirac's theorem

Between "chordal" and "has a simplicial elimination ordering" stands a theorem — Dirac's
{citep dirac}[] — and the paper takes it for granted, as papers reasonably do. A formalization
cannot. Either the ordering form is proved and the chordal statement is left as a informal gloss, or
Dirac's theorem is proved too.

Here it is proved. The heart of it is the following, which is a statement about graph structure with
no colouring in it at all:

```lean
open SimpleGraph in
example {V : Type} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [Nonempty V]
    (hG : G.IsChordal) :
    ∃ v, G.IsSimplicialVertex v :=
  exists_isSimplicialVertex G hG
```

*Every nonempty finite chordal graph has a simplicial vertex.* Given that, induction on the number
of vertices produces the ordering: peel off a simplicial vertex, recurse on what is left — still
chordal, by the deletion lemma above — and put the vertex back. The converse direction is the cone
lemma, already stated. So chordality and the existence of an elimination ordering are the same
condition:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.IsChordal ↔ ∃ (k : ℕ) (d : CliqueTowerData (Fin 0) k),
      CliqueTowerData.IsSimplicial (⊥ : SimpleGraph (Fin 0)) k d ∧
        Nonempty (G ≃g cliqueTower (⊥ : SimpleGraph (Fin 0)) k d) :=
  isChordal_iff_exists_cliqueTower G
```

The ordering is presented backwards and constructively, as a tower over the empty graph, rather than
as a list of vertices with a property. That is a formalization choice with a real payoff: the tower
*is* the induction, so the theorems above apply to it directly with no translation step.

# The theorem

Putting the two halves together gives Kostochka and Sidorenko's result under its own name, with no
hypothesis borrowed and no tower data in the statement:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsChordal) (n : ℕ) :
    G.ECCAt n :=
  ecc_of_isChordal G hG n
```

*Every chordal graph is enumeratively chromatic-choosable at `n`, for every `n`.*

# Two corollaries

*Complete graphs.* $`K_m` is chordal — trivially, and also because coning repeatedly over the whole
vertex set builds it:

```lean
open SimpleGraph in
example (V : Type) [Fintype V] [DecidableEq V] (n : ℕ) :
    (⊤ : SimpleGraph V).ECCAt n :=
  ecc_top V n
```

There is a satisfying reason this had to come out true. For a complete graph *every* `n`-list
assignment with `n ≥ m` has the same number of colourings as any other? No — that is false. What is
true is that the uniform one is worst, and the counting identity above shows why: at each vertex the
number of available colours is $`n` minus the number of *distinct* colours already used on the
clique, and identical lists are exactly the situation in which all of those distinct colours are
guaranteed to be unavailable.

*Trees.* A tree has no cycles at all, so it is chordal vacuously, and every leaf is simplicial. In
the development a tree is built as a tower of pendant attachments, and each such attachment is a
cone over a singleton — a one-element set being a clique:

```lean
open SimpleGraph in
example (n k : ℕ) (d : TowerData (Fin 1) k) :
    (pendantTower (⊤ : SimpleGraph (Fin 1)) k d).ECCAt n :=
  (ecc_pendantTower_iff n k d).mpr (ecc_top (Fin 1) n)
```

Every tree, every `n`. Concretely: a tree on `v` vertices has $`n(n-1)^{v-1}` colourings from a
uniform palette, and no assignment of `n`-lists can do better.

# What is not covered

The smallest graph that escapes this chapter is the four-cycle, and the reason is exactly the reason
Dirac's theorem is about cycles: a cycle of length four or more has no simplicial vertex at all.
Every vertex of $`C_4` has two neighbours, and they are not adjacent. The cone argument never gets
started, and nothing above says anything about whether cycles are enumeratively chromatic-choosable.

They are — for every length and every `n` — but that is a genuinely harder theorem, and it is
{ref "theorem1"}[the subject of the next chapter].
