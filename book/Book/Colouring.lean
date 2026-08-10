import VersoManual
import Book.Papers
import Monophilic

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Book

set_option pp.rawOnError true
set_option maxHeartbeats 1000000

#doc (Manual) "Colouring a Graph" =>

%%%
tag := "colouring"
%%%

Source: [Defs.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Defs.lean), [Basic.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Basic.lean), [Cone.lean](https://github.com/rkirov/list-color-function/blob/main/Monophilic/Cone.lean).

This chapter assumes you know what a graph is — a finite set of vertices, some pairs of which are
joined by an edge — and nothing further. Everything else is built here.

# Proper colourings

Hand out colours to the vertices of a graph. The colouring is *proper* when no edge has the same
colour at both ends. That is the entire definition; the subject consists of asking, over and over,
how many proper colourings there are and what forces that number up or down.

```diagram (cssWidth := "70%")
open Illuminate Diagram in
let red   : Fill := .solid { color := { r := 214, g := 96, b := 77 } }
let blue  : Fill := .solid { color := { r := 70, g := 118, b := 180 } }
let gold  : Fill := .solid { color := { r := 232, g := 184, b := 70 } }
let v (x y : Float) (f : Fill) : Diagram _ := translate x y (circle 12 f)
let e (x1 y1 x2 y2 : Float) : Diagram _ := line ⟨x1, y1⟩ ⟨x2, y2⟩
let edges :=
  [e 0 90 (-110) 0, e 0 90 110 0, e (-110) 0 110 0,
   e (-110) 0 (-110) (-110), e 110 0 110 (-110), e (-110) (-110) 110 (-110)]
let verts :=
  [v 0 90 red, v (-110) 0 blue, v 110 0 gold, v (-110) (-110) red, v 110 (-110) blue]
let labels :=
  [translate 0 118 (text "a : 1"), translate (-150) 22 (text "b : 2"),
   translate 150 22 (text "c : 3"), translate (-150) (-132) (text "d : 1"),
   translate 150 (-132) (text "e : 2")]
(edges ++ verts ++ labels).foldl atop emptyDiagram
```

Every edge above joins two different colours, so this is proper. Three colours were needed: `a`, `b`
and `c` are pairwise joined, so they must all differ. Two colours would not have sufficed.

In Lean a colouring is just a function from vertices to colours, and colours are natural numbers.
Properness is the obvious predicate on such a function:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℕ) :
    G.IsProperColoring f ↔ ∀ ⦃v w⦄, G.Adj v w → f v ≠ f w :=
  Iff.rfl
```

Nothing is bundled: `f` is an ordinary function, and `G.IsProperColoring f` is an ordinary
proposition about it. That choice is what will let us *count* colourings later without fighting the
type theory.

# The chromatic number

A graph is `n`-colourable when some proper colouring uses only the colours $`\{0, \dots, n-1\}`.
The chromatic number $`\chi(G)` is the least such `n`. Four facts pin down the examples that recur
throughout this book.

*The complete graph $`K_m`* — every pair of its `m` vertices joined — needs a different colour at
every vertex, so $`\chi(K_m) = m`.

*A bipartite graph* — one whose vertices split into two sides with every edge crossing between them
— is `2`-colourable: colour one side `0` and the other `1`. In fact `2`-colourable and bipartite are
the same condition.

*A path or a tree* is bipartite, hence $`\chi = 2` as soon as it has an edge. Colour a tree by
walking outward from a root, alternating.

*A cycle* $`C_v` on `v` vertices is bipartite exactly when `v` is even. So $`\chi(C_v) = 2` for even
`v` and `3` for odd `v` — the smallest graph in this book whose answer depends on a parity.

Mathlib already has `SimpleGraph.Colorable` for the existence question, and this development links
it to the counting world by a single lemma, proved once and used everywhere:

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ} :
    G.colConst n = 0 ↔ ¬ G.Colorable n :=
  colConst_eq_zero_iff_not_colorable
```

Here `G.colConst n` is the object of the next section: the *number* of proper colourings from the
palette $`\{0, \dots, n-1\}`. The lemma says that this number vanishes precisely below the chromatic
number, which is the only fact about $`\chi` we shall ever need.

# From deciding to counting

Existence is a yes-or-no question, and it is the classical one. This book is about the finer
question: given `n` colours, *how many* proper colourings are there?

Write $`\mathrm{col}(G, n)` for that count. In Lean it is `G.colConst n`, and it is defined exactly
as you would define it by hand — take all functions from vertices to the palette, and keep the
proper ones:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    G.colConst n = ((Fintype.piFinset (fun _ => range n)).filter G.IsProperColoring).card :=
  rfl
```

Because the definition is this direct, small cases can simply be computed by the kernel, and every
number quoted below is checked rather than asserted. The triangle with three colours:

```lean
open SimpleGraph in
example : (⊤ : SimpleGraph (Fin 3)).colConst 3 = 6 := by decide
```

Six: the first vertex has three choices, the second two, the third one. With only two colours there
is nothing at all:

```lean
open SimpleGraph in
example : (⊤ : SimpleGraph (Fin 3)).colConst 2 = 0 := by decide
```

# Five families to keep in mind

*Complete graphs.* $`\mathrm{col}(K_m, n) = n(n-1)\cdots(n-m+1)`: colour the vertices one at a time,
each avoiding all those already coloured. The general form of that step is the identity that opens
the technical half of this book — attach a new vertex to a clique `K` and the count is multiplied by
exactly $`n - |K|`:

```lean
open Finset SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {K : Finset V}
    (hK : G.IsClique (K : Set V)) (n : ℕ) :
    (coneOn G K).colConst n = (n - K.card) * G.colConst n :=
  colConst_coneOn hK n
```

*Trees and paths.* A tree is built by attaching vertices of degree one, which is the case `|K| = 1`
of the same identity: each attachment multiplies the count by `n - 1`.

```lean
open SimpleGraph in
example {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (n : ℕ) :
    (coneOn G {v}).colConst n = (n - 1) * G.colConst n :=
  colConst_coneOn_singleton v n
```

So a tree on `v` vertices has $`n(n-1)^{v-1}` proper colourings, whatever its shape. The path on
three vertices with three colours has $`3 \cdot 2 \cdot 2 = 12`:

```lean
open Monophilic in
example : (pathG 2).colConst 3 = 12 := by decide
```

and the path on four vertices with two colours has $`2 \cdot 1 \cdot 1 \cdot 1 = 2` — the two
alternating colourings:

```lean
open Monophilic in
example : (pathG 3).colConst 2 = 2 := by decide
```

(In this development `pathG k` is the path with `k` edges, hence `k + 1` vertices.)

*Cycles.* Here the recursion above does not apply, because closing a cycle attaches a vertex to two
vertices that are *not* adjacent to each other. The answer, derived in a later chapter, is
$`(n-1)^v + (-1)^v (n-1)` for the cycle on `v` vertices. Two instances: the four-cycle with two
colours has $`1 + 1 = 2` colourings, and the five-cycle with two colours has none.

```lean
open Monophilic in
example : (closePath 3).colConst 2 = 2 := by decide
```

```lean
open Monophilic in
example : (closePath 4).colConst 2 = 0 := by decide
```

(`closePath k` is `pathG k` with its two ends joined, so it is the cycle on `k + 1` vertices.)

*Bipartite graphs.* Being `2`-colourable, they have at least the two colourings that use one colour
per side — and often exactly those two. The complete bipartite graph $`K_{2,3}`, two vertices on one
side joined to all three on the other, is the smallest example that will matter later. Count it by
splitting on whether the two left vertices get the same colour: if they do, `n` ways, each right
vertex then has `n - 1` choices; if they do not, $`n(n-1)` ways, and each right vertex has `n - 2`.
So $`\mathrm{col}(K_{2,3}, n) = n(n-1)^3 + n(n-1)(n-2)^3`, which is `2` at `n = 2` and `30` at
`n = 3`:

```lean
open SimpleGraph in
example : (completeBipartiteGraph (Fin 2) (Fin 3)).colConst 2 = 2 :=
  colConst_completeBipartite_two_three_two
```

```lean
open SimpleGraph in
example : (completeBipartiteGraph (Fin 2) (Fin 3)).colConst 3 = 30 := by decide
```

*Graphs with no edges.* $`\mathrm{col} = n^{|V|}`, the largest the count can be. Every constraint
removed is a factor of `n` regained.

The table collects the counts for the graphs above. Each row is a function of `n`, and this is the
first hint of the next chapter: those functions are all polynomials.

:::table +header (align := left)
*
  * Graph
  * $`\chi`
  * $`\mathrm{col}(G, n)`
*
  * no edges, `v` vertices
  * `1`
  * $`n^{v}`
*
  * tree, `v` vertices
  * `2`
  * $`n(n-1)^{v-1}`
*
  * complete graph $`K_m`
  * `m`
  * $`n(n-1)\cdots(n-m+1)`
*
  * cycle $`C_v`
  * `2` or `3`
  * $`(n-1)^{v} + (-1)^{v}(n-1)`
*
  * $`K_{2,3}`
  * `2`
  * $`n(n-1)^3 + n(n-1)(n-2)^3`
:::

The last entry is the odd one out. The first four rows are formulas one can guess from the shape of
the graph; the fifth had to be computed. $`K_{2,3}` is exactly the sort of graph — small, bipartite,
unremarkable — that will turn out to sit on the boundary of the classification in
{ref "twomonophilic"}[a later chapter].

# The question this book is about

All of the above hands every vertex the *same* palette. The subject of this book begins when each
vertex is given its own private list of permitted colours, and the count is compared against the
uniform case. Before that, {ref "polynomial"}[the next chapter] establishes the one structural fact
about $`\mathrm{col}(G, n)` that makes the comparison meaningful: it is a polynomial in `n`.
